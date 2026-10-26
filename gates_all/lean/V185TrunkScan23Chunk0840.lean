import V185TrunkScan23Chunk0839

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4970993 : List Nat := [1, 2, 2, 2, 3, 1, 1, 1, 2, 2, 6]
def baseStart_4970993 : Nat := 118140960795 + 4970993 * 2 ^ 59
def prefixEnd_4970993 : Nat := 4983230072969 + 3 ^ 40 * 4970993 * 2
def baseEnd_4970993 : Nat := 2552508739135574700726325

theorem tailTrace_4970993 : CollatzResearch.WordTrace tailWord_4970993 prefixEnd_4970993 2552508739135574700726325 := by
  unfold tailWord_4970993
  simp only [CollatzResearch.WordTrace]
  refine ⟨181307009679948813858917633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120871339786632542572611755 181307009679948813858917633)
  ·
    refine ⟨135980257259961610394188225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181307009679948813858917633 135980257259961610394188225)
    ·
      refine ⟨101985192944971207795641169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135980257259961610394188225 101985192944971207795641169)
      ·
        refine ⟨76488894708728405846730877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101985192944971207795641169 76488894708728405846730877)
        ·
          refine ⟨28683335515773152192524079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76488894708728405846730877 28683335515773152192524079)
          ·
            refine ⟨43025003273659728288786119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28683335515773152192524079 43025003273659728288786119)
            ·
              refine ⟨64537504910489592433179179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43025003273659728288786119 64537504910489592433179179)
              ·
                refine ⟨96806257365734388649768769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64537504910489592433179179 96806257365734388649768769)
                ·
                  refine ⟨72604693024300791487326577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 96806257365734388649768769 72604693024300791487326577)
                  ·
                    refine ⟨54453519768225593615494933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 72604693024300791487326577 54453519768225593615494933)
                    ·
                      refine ⟨2552508739135574700726325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54453519768225593615494933 2552508739135574700726325)
                      ·
                        rfl

theorem cell23_4970993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_4970993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4970993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4970993 prefixEnd_4970993 := by exact prefixLift 4970993
  have htrace : WordTrace (prefixWord ++ tailWord_4970993) baseStart_4970993 baseEnd_4970993 := by
    simpa [prefixWord, tailWord_4970993, baseEnd_4970993] using wordTrace_append hprefix tailTrace_4970993
  have hstable : (prefixWord ++ tailWord_4970993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4970993).length < 2 ^ (prefixWord ++ tailWord_4970993).sum := by decide
  have hdescent : baseEnd_4970993 < baseStart_4970993 := by decide
  rcases family_descends (prefixWord ++ tailWord_4970993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4970994 : List Nat := [3, 2, 1, 4, 2, 1, 1, 3, 2, 4]
def baseStart_4970994 : Nat := 118140960795 + 4970994 * 2 ^ 59
def prefixEnd_4970994 : Nat := 4983230072969 + 3 ^ 40 * 4970994 * 2
def baseEnd_4970994 : Nat := 850836417538743065604607

theorem tailTrace_4970994 : CollatzResearch.WordTrace tailWord_4970994 prefixEnd_4970994 850836417538743065604607 := by
  unfold tailWord_4970994
  simp only [CollatzResearch.WordTrace]
  refine ⟨45326761538236297757426009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120871364101963460686469357 45326761538236297757426009)
  ·
    refine ⟨33995071153677223318069507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45326761538236297757426009 33995071153677223318069507)
    ·
      refine ⟨50992606730515834977104261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33995071153677223318069507 50992606730515834977104261)
      ·
        refine ⟨9561113761971719058207049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50992606730515834977104261 9561113761971719058207049)
        ·
          refine ⟨7170835321478789293655287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9561113761971719058207049 7170835321478789293655287)
          ·
            refine ⟨10756252982218183940482931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7170835321478789293655287 10756252982218183940482931)
            ·
              refine ⟨16134379473327275910724397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10756252982218183940482931 16134379473327275910724397)
              ·
                refine ⟨6050392302497728466521649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16134379473327275910724397 6050392302497728466521649)
                ·
                  refine ⟨4537794226873296349891237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6050392302497728466521649 4537794226873296349891237)
                  ·
                    refine ⟨850836417538743065604607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4537794226873296349891237 850836417538743065604607)
                    ·
                      rfl

theorem cell23_4970994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 3, 2, 4].length) (baseStart_4970994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4970994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4970994 prefixEnd_4970994 := by exact prefixLift 4970994
  have htrace : WordTrace (prefixWord ++ tailWord_4970994) baseStart_4970994 baseEnd_4970994 := by
    simpa [prefixWord, tailWord_4970994, baseEnd_4970994] using wordTrace_append hprefix tailTrace_4970994
  have hstable : (prefixWord ++ tailWord_4970994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4970994).length < 2 ^ (prefixWord ++ tailWord_4970994).sum := by decide
  have hdescent : baseEnd_4970994 < baseStart_4970994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4970994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4971000 : List Nat := [2, 1, 2, 1, 1, 4, 2, 3, 1, 3, 3]
def baseStart_4971000 : Nat := 118140960795 + 4971000 * 2 ^ 59
def prefixEnd_4971000 : Nat := 4983230072969 + 3 ^ 40 * 4971000 * 2
def baseEnd_4971000 : Nat := 2552512333500156173338793

theorem tailTrace_4971000 : CollatzResearch.WordTrace tailWord_4971000 prefixEnd_4971000 2552512333500156173338793 := by
  unfold tailWord_4971000
  simp only [CollatzResearch.WordTrace]
  refine ⟨90653632495461727027211227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120871509993948969369614969 90653632495461727027211227)
  ·
    refine ⟨135980448743192590540816841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90653632495461727027211227 135980448743192590540816841)
    ·
      refine ⟨101985336557394442905612631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135980448743192590540816841 101985336557394442905612631)
      ·
        refine ⟨152978004836091664358418947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101985336557394442905612631 152978004836091664358418947)
        ·
          refine ⟨229467007254137496537628421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152978004836091664358418947 229467007254137496537628421)
          ·
            refine ⟨43025063860150780600805329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 229467007254137496537628421 43025063860150780600805329)
            ·
              refine ⟨32268797895113085450603997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43025063860150780600805329 32268797895113085450603997)
              ·
                refine ⟨12100799210667407043976499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32268797895113085450603997 12100799210667407043976499)
                ·
                  refine ⟨18151198816001110565964749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12100799210667407043976499 18151198816001110565964749)
                  ·
                    refine ⟨6806699556000416462236781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18151198816001110565964749 6806699556000416462236781)
                    ·
                      refine ⟨2552512333500156173338793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6806699556000416462236781 2552512333500156173338793)
                      ·
                        rfl

theorem cell23_4971000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 3, 1, 3, 3].length) (baseStart_4971000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4971000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4971000 prefixEnd_4971000 := by exact prefixLift 4971000
  have htrace : WordTrace (prefixWord ++ tailWord_4971000) baseStart_4971000 baseEnd_4971000 := by
    simpa [prefixWord, tailWord_4971000, baseEnd_4971000] using wordTrace_append hprefix tailTrace_4971000
  have hstable : (prefixWord ++ tailWord_4971000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4971000).length < 2 ^ (prefixWord ++ tailWord_4971000).sum := by decide
  have hdescent : baseEnd_4971000 < baseStart_4971000 := by decide
  rcases family_descends (prefixWord ++ tailWord_4971000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4971013 : List Nat := [1, 3, 1, 1, 2, 2, 2, 1, 1, 4, 5]
def baseStart_4971013 : Nat := 118140960795 + 4971013 * 2 ^ 59
def prefixEnd_4971013 : Nat := 4983230072969 + 3 ^ 40 * 4971013 * 2
def baseEnd_4971013 : Nat := 2552519008748664622476233

theorem tailTrace_4971013 : CollatzResearch.WordTrace tailWord_4971013 prefixEnd_4971013 2552519008748664622476233 := by
  unfold tailWord_4971013
  simp only [CollatzResearch.WordTrace]
  refine ⟨181307739139876357274645693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120871826093250904849763795 181307739139876357274645693)
  ·
    refine ⟨67990402177453633977992135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181307739139876357274645693 67990402177453633977992135)
    ·
      refine ⟨101985603266180450966988203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67990402177453633977992135 101985603266180450966988203)
      ·
        refine ⟨152978404899270676450482305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101985603266180450966988203 152978404899270676450482305)
        ·
          refine ⟨114733803674453007337861729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152978404899270676450482305 114733803674453007337861729)
          ·
            refine ⟨86050352755839755503396297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114733803674453007337861729 86050352755839755503396297)
            ·
              refine ⟨64537764566879816627547223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86050352755839755503396297 64537764566879816627547223)
              ·
                refine ⟨96806646850319724941320835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64537764566879816627547223 96806646850319724941320835)
                ·
                  refine ⟨145209970275479587411981253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96806646850319724941320835 145209970275479587411981253)
                  ·
                    refine ⟨27226869426652422639746485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 145209970275479587411981253 27226869426652422639746485)
                    ·
                      refine ⟨2552519008748664622476233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27226869426652422639746485 2552519008748664622476233)
                      ·
                        rfl

theorem cell23_4971013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 4, 5].length) (baseStart_4971013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4971013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4971013 prefixEnd_4971013 := by exact prefixLift 4971013
  have htrace : WordTrace (prefixWord ++ tailWord_4971013) baseStart_4971013 baseEnd_4971013 := by
    simpa [prefixWord, tailWord_4971013, baseEnd_4971013] using wordTrace_append hprefix tailTrace_4971013
  have hstable : (prefixWord ++ tailWord_4971013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4971013).length < 2 ^ (prefixWord ++ tailWord_4971013).sum := by decide
  have hdescent : baseEnd_4971013 < baseStart_4971013 := by decide
  rcases family_descends (prefixWord ++ tailWord_4971013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4971021 : List Nat := [1, 7, 1, 1, 1, 3, 1, 1, 1, 1, 5]
def baseStart_4971021 : Nat := 118140960795 + 4971021 * 2 ^ 59
def prefixEnd_4971021 : Nat := 4983230072969 + 3 ^ 40 * 4971021 * 2
def baseEnd_4971021 : Nat := 2552523116593900591176197

theorem tailTrace_4971021 : CollatzResearch.WordTrace tailWord_4971021 prefixEnd_4971021 2552523116593900591176197 := by
  unfold tailWord_4971021
  simp only [CollatzResearch.WordTrace]
  refine ⟨181308030923847374640936917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120872020615898249760624611 181308030923847374640936917)
  ·
    refine ⟨4249406974777672843146959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 181308030923847374640936917 4249406974777672843146959)
    ·
      refine ⟨6374110462166509264720439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4249406974777672843146959 6374110462166509264720439)
      ·
        refine ⟨9561165693249763897080659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6374110462166509264720439 9561165693249763897080659)
        ·
          refine ⟨14341748539874645845620989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9561165693249763897080659 14341748539874645845620989)
          ·
            refine ⟨5378155702452992192107871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14341748539874645845620989 5378155702452992192107871)
            ·
              refine ⟨8067233553679488288161807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5378155702452992192107871 8067233553679488288161807)
              ·
                refine ⟨12100850330519232432242711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8067233553679488288161807 12100850330519232432242711)
                ·
                  refine ⟨18151275495778848648364067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12100850330519232432242711 18151275495778848648364067)
                  ·
                    refine ⟨27226913243668272972546101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18151275495778848648364067 27226913243668272972546101)
                    ·
                      refine ⟨2552523116593900591176197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27226913243668272972546101 2552523116593900591176197)
                      ·
                        rfl

theorem cell23_4971021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_4971021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4971021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4971021 prefixEnd_4971021 := by exact prefixLift 4971021
  have htrace : WordTrace (prefixWord ++ tailWord_4971021) baseStart_4971021 baseEnd_4971021 := by
    simpa [prefixWord, tailWord_4971021, baseEnd_4971021] using wordTrace_append hprefix tailTrace_4971021
  have hstable : (prefixWord ++ tailWord_4971021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4971021).length < 2 ^ (prefixWord ++ tailWord_4971021).sum := by decide
  have hdescent : baseEnd_4971021 < baseStart_4971021 := by decide
  rcases family_descends (prefixWord ++ tailWord_4971021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4971023 : List Nat := [1, 1, 2, 1, 1, 1, 2, 4, 1, 5, 4]
def baseStart_4971023 : Nat := 118140960795 + 4971023 * 2 ^ 59
def prefixEnd_4971023 : Nat := 4983230072969 + 3 ^ 40 * 4971023 * 2
def baseEnd_4971023 : Nat := 2552524143555209583351187

theorem tailTrace_4971023 : CollatzResearch.WordTrace tailWord_4971023 prefixEnd_4971023 2552524143555209583351187 := by
  unfold tailWord_4971023
  simp only [CollatzResearch.WordTrace]
  refine ⟨181308103869840128982509723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120872069246560085988339815 181308103869840128982509723)
  ·
    refine ⟨271962155804760193473764585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181308103869840128982509723 271962155804760193473764585)
    ·
      refine ⟨203971616853570145105323439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 271962155804760193473764585 203971616853570145105323439)
      ·
        refine ⟨305957425280355217657985159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203971616853570145105323439 305957425280355217657985159)
        ·
          refine ⟨458936137920532826486977739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 305957425280355217657985159 458936137920532826486977739)
          ·
            refine ⟨688404206880799239730466609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 458936137920532826486977739 688404206880799239730466609)
            ·
              refine ⟨516303155160599429797849957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 688404206880799239730466609 516303155160599429797849957)
              ·
                refine ⟨96806841592612393087096867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 516303155160599429797849957 96806841592612393087096867)
                ·
                  refine ⟨145210262388918589630645301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96806841592612393087096867 145210262388918589630645301)
                  ·
                    refine ⟨13613462098961117777872997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 145210262388918589630645301 13613462098961117777872997)
                    ·
                      refine ⟨2552524143555209583351187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13613462098961117777872997 2552524143555209583351187)
                      ·
                        rfl

theorem cell23_4971023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 5, 4].length) (baseStart_4971023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4971023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4971023 prefixEnd_4971023 := by exact prefixLift 4971023
  have htrace : WordTrace (prefixWord ++ tailWord_4971023) baseStart_4971023 baseEnd_4971023 := by
    simpa [prefixWord, tailWord_4971023, baseEnd_4971023] using wordTrace_append hprefix tailTrace_4971023
  have hstable : (prefixWord ++ tailWord_4971023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4971023).length < 2 ^ (prefixWord ++ tailWord_4971023).sum := by decide
  have hdescent : baseEnd_4971023 < baseStart_4971023 := by decide
  rcases family_descends (prefixWord ++ tailWord_4971023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4971033 : List Nat := [1, 2, 1, 2, 1, 1, 2, 3, 4, 6]
def baseStart_4971033 : Nat := 118140960795 + 4971033 * 2 ^ 59
def prefixEnd_4971033 : Nat := 4983230072969 + 3 ^ 40 * 4971033 * 2
def baseEnd_4971033 : Nat := 850843092787251514742047

theorem tailTrace_4971033 : CollatzResearch.WordTrace tailWord_4971033 prefixEnd_4971033 850843092787251514742047 := by
  unfold tailWord_4971033
  simp only [CollatzResearch.WordTrace]
  refine ⟨181308468599803900690373753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120872312399869267126915835 181308468599803900690373753)
  ·
    refine ⟨135981351449852925517780315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181308468599803900690373753 135981351449852925517780315)
    ·
      refine ⟨203972027174779388276670473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135981351449852925517780315 203972027174779388276670473)
      ·
        refine ⟨152979020381084541207502855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203972027174779388276670473 152979020381084541207502855)
        ·
          refine ⟨229468530571626811811254283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152979020381084541207502855 229468530571626811811254283)
          ·
            refine ⟨344202795857440217716881425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229468530571626811811254283 344202795857440217716881425)
            ·
              refine ⟨258152096893080163287661069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 344202795857440217716881425 258152096893080163287661069)
              ·
                refine ⟨96807036334905061232872901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 258152096893080163287661069 96807036334905061232872901)
                ·
                  refine ⟨18151319312794698981163669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 96807036334905061232872901 18151319312794698981163669)
                  ·
                    refine ⟨850843092787251514742047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18151319312794698981163669 850843092787251514742047)
                    ·
                      rfl

theorem cell23_4971033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 4, 6].length) (baseStart_4971033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4971033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4971033 prefixEnd_4971033 := by exact prefixLift 4971033
  have htrace : WordTrace (prefixWord ++ tailWord_4971033) baseStart_4971033 baseEnd_4971033 := by
    simpa [prefixWord, tailWord_4971033, baseEnd_4971033] using wordTrace_append hprefix tailTrace_4971033
  have hstable : (prefixWord ++ tailWord_4971033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4971033).length < 2 ^ (prefixWord ++ tailWord_4971033).sum := by decide
  have hdescent : baseEnd_4971033 < baseStart_4971033 := by decide
  rcases family_descends (prefixWord ++ tailWord_4971033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4971050 : List Nat := [3, 1, 4, 1, 1, 2, 1, 1, 1, 8]
def baseStart_4971050 : Nat := 118140960795 + 4971050 * 2 ^ 59
def prefixEnd_4971050 : Nat := 4983230072969 + 3 ^ 40 * 4971050 * 2
def baseEnd_4971050 : Nat := 850846002510960325904521

theorem tailTrace_4971050 : CollatzResearch.WordTrace tailWord_4971050 prefixEnd_4971050 850846002510960325904521 := by
  unfold tailWord_4971050
  simp only [CollatzResearch.WordTrace]
  refine ⟨45327272160185578148435651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120872725760494875062495069 45327272160185578148435651)
  ·
    refine ⟨67990908240278367222653477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45327272160185578148435651 67990908240278367222653477)
    ·
      refine ⟨12748295295052193854247527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67990908240278367222653477 12748295295052193854247527)
      ·
        refine ⟨19122442942578290781371291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12748295295052193854247527 19122442942578290781371291)
        ·
          refine ⟨28683664413867436172056937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19122442942578290781371291 28683664413867436172056937)
          ·
            refine ⟨21512748310400577129042703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28683664413867436172056937 21512748310400577129042703)
            ·
              refine ⟨32269122465600865693564055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21512748310400577129042703 32269122465600865693564055)
              ·
                refine ⟨48403683698401298540346083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32269122465600865693564055 48403683698401298540346083)
                ·
                  refine ⟨72605525547601947810519125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48403683698401298540346083 72605525547601947810519125)
                  ·
                    refine ⟨850846002510960325904521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 72605525547601947810519125 850846002510960325904521)
                    ·
                      rfl

theorem cell23_4971050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_4971050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4971050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4971050 prefixEnd_4971050 := by exact prefixLift 4971050
  have htrace : WordTrace (prefixWord ++ tailWord_4971050) baseStart_4971050 baseEnd_4971050 := by
    simpa [prefixWord, tailWord_4971050, baseEnd_4971050] using wordTrace_append hprefix tailTrace_4971050
  have hstable : (prefixWord ++ tailWord_4971050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4971050).length < 2 ^ (prefixWord ++ tailWord_4971050).sum := by decide
  have hdescent : baseEnd_4971050 < baseStart_4971050 := by decide
  rcases family_descends (prefixWord ++ tailWord_4971050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4971057 : List Nat := [1, 2, 2, 3, 1, 1, 3, 3, 1, 4, 2]
def baseStart_4971057 : Nat := 118140960795 + 4971057 * 2 ^ 59
def prefixEnd_4971057 : Nat := 4983230072969 + 3 ^ 40 * 4971057 * 2
def baseEnd_4971057 : Nat := 2552541601897462450326031

theorem tailTrace_4971057 : CollatzResearch.WordTrace tailWord_4971057 prefixEnd_4971057 2552541601897462450326031 := by
  unfold tailWord_4971057
  simp only [CollatzResearch.WordTrace]
  refine ⟨181309343951716952789247425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120872895967811301859498283 181309343951716952789247425)
  ·
    refine ⟨135982007963787714591935569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181309343951716952789247425 135982007963787714591935569)
    ·
      refine ⟨101986505972840785943951677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135982007963787714591935569 101986505972840785943951677)
      ·
        refine ⟨38244939739815294728981879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101986505972840785943951677 38244939739815294728981879)
        ·
          refine ⟨57367409609722942093472819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38244939739815294728981879 57367409609722942093472819)
          ·
            refine ⟨86051114414584413140209229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57367409609722942093472819 86051114414584413140209229)
            ·
              refine ⟨32269167905469154927578461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86051114414584413140209229 32269167905469154927578461)
              ·
                refine ⟨12100937964550933097841923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32269167905469154927578461 12100937964550933097841923)
                ·
                  refine ⟨18151406946826399646762885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12100937964550933097841923 18151406946826399646762885)
                  ·
                    refine ⟨3403388802529949933768041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18151406946826399646762885 3403388802529949933768041)
                    ·
                      refine ⟨2552541601897462450326031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3403388802529949933768041 2552541601897462450326031)
                      ·
                        rfl

theorem cell23_4971057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 3, 1, 4, 2].length) (baseStart_4971057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4971057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4971057 prefixEnd_4971057 := by exact prefixLift 4971057
  have htrace : WordTrace (prefixWord ++ tailWord_4971057) baseStart_4971057 baseEnd_4971057 := by
    simpa [prefixWord, tailWord_4971057, baseEnd_4971057] using wordTrace_append hprefix tailTrace_4971057
  have hstable : (prefixWord ++ tailWord_4971057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4971057).length < 2 ^ (prefixWord ++ tailWord_4971057).sum := by decide
  have hdescent : baseEnd_4971057 < baseStart_4971057 := by decide
  rcases family_descends (prefixWord ++ tailWord_4971057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4971078 : List Nat := [6, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2]
def baseStart_4971078 : Nat := 118140960795 + 4971078 * 2 ^ 59
def prefixEnd_4971078 : Nat := 4983230072969 + 3 ^ 40 * 4971078 * 2
def baseEnd_4971078 : Nat := 2552552384991206868163435

theorem tailTrace_4971078 : CollatzResearch.WordTrace tailWord_4971078 prefixEnd_4971078 2552552384991206868163435 := by
  unfold tailWord_4971078
  simp only [CollatzResearch.WordTrace]
  refine ⟨5665940933895027292992559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 120873406589760582250507925 5665940933895027292992559)
  ·
    refine ⟨8498911400842540939488839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5665940933895027292992559 8498911400842540939488839)
    ·
      refine ⟨12748367101263811409233259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8498911400842540939488839 12748367101263811409233259)
      ·
        refine ⟨19122550651895717113849889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12748367101263811409233259 19122550651895717113849889)
        ·
          refine ⟨14341912988921787835387417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19122550651895717113849889 14341912988921787835387417)
          ·
            refine ⟨10756434741691340876540563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14341912988921787835387417 10756434741691340876540563)
            ·
              refine ⟨16134652112537011314810845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10756434741691340876540563 16134652112537011314810845)
              ·
                refine ⟨6050494542201379243054067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16134652112537011314810845 6050494542201379243054067)
                ·
                  refine ⟨9075741813302068864581101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6050494542201379243054067 9075741813302068864581101)
                  ·
                    refine ⟨3403403179988275824217913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9075741813302068864581101 3403403179988275824217913)
                    ·
                      refine ⟨2552552384991206868163435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3403403179988275824217913 2552552384991206868163435)
                      ·
                        rfl

theorem cell23_4971078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2].length) (baseStart_4971078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4971078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4971078 prefixEnd_4971078 := by exact prefixLift 4971078
  have htrace : WordTrace (prefixWord ++ tailWord_4971078) baseStart_4971078 baseEnd_4971078 := by
    simpa [prefixWord, tailWord_4971078, baseEnd_4971078] using wordTrace_append hprefix tailTrace_4971078
  have hstable : (prefixWord ++ tailWord_4971078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4971078).length < 2 ^ (prefixWord ++ tailWord_4971078).sum := by decide
  have hdescent : baseEnd_4971078 < baseStart_4971078 := by decide
  rcases family_descends (prefixWord ++ tailWord_4971078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4971102 : List Nat := [4, 4, 1, 2, 1, 1, 3, 1, 2, 1, 3]
def baseStart_4971102 : Nat := 118140960795 + 4971102 * 2 ^ 59
def prefixEnd_4971102 : Nat := 4983230072969 + 3 ^ 40 * 4971102 * 2
def baseEnd_4971102 : Nat := 2552564708526914774263325

theorem tailTrace_4971102 : CollatzResearch.WordTrace tailWord_4971102 prefixEnd_4971102 2552564708526914774263325 := by
  unfold tailWord_4971102
  simp only [CollatzResearch.WordTrace]
  refine ⟨22663873154569240684329445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120873990157702616983090373 22663873154569240684329445)
  ·
    refine ⟨4249476216481732628311771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22663873154569240684329445 4249476216481732628311771)
    ·
      refine ⟨6374214324722598942467657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4249476216481732628311771 6374214324722598942467657)
      ·
        refine ⟨4780660743541949206850743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6374214324722598942467657 4780660743541949206850743)
        ·
          refine ⟨7170991115312923810276115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4780660743541949206850743 7170991115312923810276115)
          ·
            refine ⟨10756486672969385715414173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7170991115312923810276115 10756486672969385715414173)
            ·
              refine ⟨4033682502363519643280315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10756486672969385715414173 4033682502363519643280315)
              ·
                refine ⟨6050523753545279464920473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4033682502363519643280315 6050523753545279464920473)
                ·
                  refine ⟨4537892815158959598690355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6050523753545279464920473 4537892815158959598690355)
                  ·
                    refine ⟨6806839222738439398035533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4537892815158959598690355 6806839222738439398035533)
                    ·
                      refine ⟨2552564708526914774263325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6806839222738439398035533 2552564708526914774263325)
                      ·
                        rfl

theorem cell23_4971102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_4971102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4971102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4971102 prefixEnd_4971102 := by exact prefixLift 4971102
  have htrace : WordTrace (prefixWord ++ tailWord_4971102) baseStart_4971102 baseEnd_4971102 := by
    simpa [prefixWord, tailWord_4971102, baseEnd_4971102] using wordTrace_append hprefix tailTrace_4971102
  have hstable : (prefixWord ++ tailWord_4971102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4971102).length < 2 ^ (prefixWord ++ tailWord_4971102).sum := by decide
  have hdescent : baseEnd_4971102 < baseStart_4971102 := by decide
  rcases family_descends (prefixWord ++ tailWord_4971102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4971147 : List Nat := [1, 1, 1, 1, 4, 1, 2, 4, 2, 4, 2]
def baseStart_4971147 : Nat := 118140960795 + 4971147 * 2 ^ 59
def prefixEnd_4971147 : Nat := 4983230072969 + 3 ^ 40 * 4971147 * 2
def baseEnd_4971147 : Nat := 2552587815156367098200617

theorem tailTrace_4971147 : CollatzResearch.WordTrace tailWord_4971147 prefixEnd_4971147 2552587815156367098200617 := by
  unfold tailWord_4971147
  simp only [CollatzResearch.WordTrace]
  refine ⟨181312626521390898160023695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120875084347593932106682463 181312626521390898160023695)
  ·
    refine ⟨271968939782086347240035543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181312626521390898160023695 271968939782086347240035543)
    ·
      refine ⟨407953409673129520860053315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271968939782086347240035543 407953409673129520860053315)
      ·
        refine ⟨611930114509694281290079973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 407953409673129520860053315 611930114509694281290079973)
        ·
          refine ⟨114736896470567677741889995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 611930114509694281290079973 114736896470567677741889995)
          ·
            refine ⟨172105344705851516612834993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114736896470567677741889995 172105344705851516612834993)
            ·
              refine ⟨129079008529388637459626245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 172105344705851516612834993 129079008529388637459626245)
              ·
                refine ⟨24202314099260369523679921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 129079008529388637459626245 24202314099260369523679921)
                ·
                  refine ⟨18151735574445277142759941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24202314099260369523679921 18151735574445277142759941)
                  ·
                    refine ⟨3403450420208489464267489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18151735574445277142759941 3403450420208489464267489)
                    ·
                      refine ⟨2552587815156367098200617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3403450420208489464267489 2552587815156367098200617)
                      ·
                        rfl

theorem cell23_4971147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 2, 4, 2].length) (baseStart_4971147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4971147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4971147 prefixEnd_4971147 := by exact prefixLift 4971147
  have htrace : WordTrace (prefixWord ++ tailWord_4971147) baseStart_4971147 baseEnd_4971147 := by
    simpa [prefixWord, tailWord_4971147, baseEnd_4971147] using wordTrace_append hprefix tailTrace_4971147
  have hstable : (prefixWord ++ tailWord_4971147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4971147).length < 2 ^ (prefixWord ++ tailWord_4971147).sum := by decide
  have hdescent : baseEnd_4971147 < baseStart_4971147 := by decide
  rcases family_descends (prefixWord ++ tailWord_4971147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4971204 : List Nat := [2, 3, 3, 1, 1, 3, 2, 2, 6]
def baseStart_4971204 : Nat := 118140960795 + 4971204 * 2 ^ 59
def prefixEnd_4971204 : Nat := 4983230072969 + 3 ^ 40 * 4971204 * 2
def baseEnd_4971204 : Nat := 283624120394852597243095

theorem tailTrace_4971204 : CollatzResearch.WordTrace tailWord_4971204 prefixEnd_4971204 283624120394852597243095 := by
  unfold tailWord_4971204
  simp only [CollatzResearch.WordTrace]
  refine ⟨90657352741092198447424333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120876470321456264596565777 90657352741092198447424333)
  ·
    refine ⟨33996507277909574417784125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90657352741092198447424333 33996507277909574417784125)
    ·
      refine ⟨12748690229216090406669047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33996507277909574417784125 12748690229216090406669047)
      ·
        refine ⟨19123035343824135610003571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12748690229216090406669047 19123035343824135610003571)
        ·
          refine ⟨28684553015736203415005357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19123035343824135610003571 28684553015736203415005357)
          ·
            refine ⟨10756707380901076280627009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28684553015736203415005357 10756707380901076280627009)
            ·
              refine ⟨8067530535675807210470257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10756707380901076280627009 8067530535675807210470257)
              ·
                refine ⟨6050647901756855407852693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8067530535675807210470257 6050647901756855407852693)
                ·
                  refine ⟨283624120394852597243095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6050647901756855407852693 283624120394852597243095)
                  ·
                    rfl

theorem cell23_4971204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 2, 6].length) (baseStart_4971204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4971204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4971204 prefixEnd_4971204 := by exact prefixLift 4971204
  have htrace : WordTrace (prefixWord ++ tailWord_4971204) baseStart_4971204 baseEnd_4971204 := by
    simpa [prefixWord, tailWord_4971204, baseEnd_4971204] using wordTrace_append hprefix tailTrace_4971204
  have hstable : (prefixWord ++ tailWord_4971204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4971204).length < 2 ^ (prefixWord ++ tailWord_4971204).sum := by decide
  have hdescent : baseEnd_4971204 < baseStart_4971204 := by decide
  rcases family_descends (prefixWord ++ tailWord_4971204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4971208 : List Nat := [2, 1, 3, 1, 2, 5, 2, 2, 1, 4]
def baseStart_4971208 : Nat := 118140960795 + 4971208 * 2 ^ 59
def prefixEnd_4971208 : Nat := 4983230072969 + 3 ^ 40 * 4971208 * 2
def baseEnd_4971208 : Nat := 850873045825430453179279

theorem tailTrace_4971208 : CollatzResearch.WordTrace tailWord_4971208 prefixEnd_4971208 850873045825430453179279 := by
  unfold tailWord_4971208
  simp only [CollatzResearch.WordTrace]
  refine ⟨90657425687084952788997139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120876567582779937051996185 90657425687084952788997139)
  ·
    refine ⟨135986138530627429183495709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90657425687084952788997139 135986138530627429183495709)
    ·
      refine ⟨50994801948985285943810891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135986138530627429183495709 50994801948985285943810891)
      ·
        refine ⟨76492202923477928915716337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50994801948985285943810891 76492202923477928915716337)
        ·
          refine ⟨57369152192608446686787253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76492202923477928915716337 57369152192608446686787253)
          ·
            refine ⟨5378358018057041876886305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57369152192608446686787253 5378358018057041876886305)
            ·
              refine ⟨4033768513542781407664729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5378358018057041876886305 4033768513542781407664729)
              ·
                refine ⟨3025326385157086055748547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4033768513542781407664729 3025326385157086055748547)
                ·
                  refine ⟨4537989577735629083622821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3025326385157086055748547 4537989577735629083622821)
                  ·
                    refine ⟨850873045825430453179279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4537989577735629083622821 850873045825430453179279)
                    ·
                      rfl

theorem cell23_4971208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 2, 2, 1, 4].length) (baseStart_4971208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4971208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4971208 prefixEnd_4971208 := by exact prefixLift 4971208
  have htrace : WordTrace (prefixWord ++ tailWord_4971208) baseStart_4971208 baseEnd_4971208 := by
    simpa [prefixWord, tailWord_4971208, baseEnd_4971208] using wordTrace_append hprefix tailTrace_4971208
  have hstable : (prefixWord ++ tailWord_4971208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4971208).length < 2 ^ (prefixWord ++ tailWord_4971208).sum := by decide
  have hdescent : baseEnd_4971208 < baseStart_4971208 := by decide
  rcases family_descends (prefixWord ++ tailWord_4971208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4971247 : List Nat := [1, 1, 2, 1, 5, 2, 2, 2, 1, 6]
def baseStart_4971247 : Nat := 118140960795 + 4971247 * 2 ^ 59
def prefixEnd_4971247 : Nat := 4983230072969 + 3 ^ 40 * 4971247 * 2
def baseEnd_4971247 : Nat := 850879721073938902316719

theorem tailTrace_4971247 : CollatzResearch.WordTrace tailWord_4971247 prefixEnd_4971247 850879721073938902316719 := by
  unfold tailWord_4971247
  simp only [CollatzResearch.WordTrace]
  refine ⟨181316273821028615238663995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120877515880685743492442663 181316273821028615238663995)
  ·
    refine ⟨271974410731542922857995993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181316273821028615238663995 271974410731542922857995993)
    ·
      refine ⟨203980808048657192143496995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 271974410731542922857995993 203980808048657192143496995)
      ·
        refine ⟨305971212072985788215245493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203980808048657192143496995 305971212072985788215245493)
        ·
          refine ⟨28684801131842417645179265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 305971212072985788215245493 28684801131842417645179265)
          ·
            refine ⟨21513600848881813233884449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28684801131842417645179265 21513600848881813233884449)
            ·
              refine ⟨16135200636661359925413337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21513600848881813233884449 16135200636661359925413337)
              ·
                refine ⟨12101400477496019944060003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16135200636661359925413337 12101400477496019944060003)
                ·
                  refine ⟨18152100716244029916090005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12101400477496019944060003 18152100716244029916090005)
                  ·
                    refine ⟨850879721073938902316719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18152100716244029916090005 850879721073938902316719)
                    ·
                      rfl

theorem cell23_4971247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 2, 1, 6].length) (baseStart_4971247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4971247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4971247 prefixEnd_4971247 := by exact prefixLift 4971247
  have htrace : WordTrace (prefixWord ++ tailWord_4971247) baseStart_4971247 baseEnd_4971247 := by
    simpa [prefixWord, tailWord_4971247, baseEnd_4971247] using wordTrace_append hprefix tailTrace_4971247
  have hstable : (prefixWord ++ tailWord_4971247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4971247).length < 2 ^ (prefixWord ++ tailWord_4971247).sum := by decide
  have hdescent : baseEnd_4971247 < baseStart_4971247 := by decide
  rcases family_descends (prefixWord ++ tailWord_4971247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4971304 : List Nat := [2, 1, 5, 1, 1, 1, 2, 1, 3, 3, 3]
def baseStart_4971304 : Nat := 118140960795 + 4971304 * 2 ^ 59
def prefixEnd_4971304 : Nat := 4983230072969 + 3 ^ 40 * 4971304 * 2
def baseEnd_4971304 : Nat := 2552668431619122983937395

theorem tailTrace_4971304 : CollatzResearch.WordTrace tailWord_4971304 prefixEnd_4971304 2552668431619122983937395 := by
  unfold tailWord_4971304
  simp only [CollatzResearch.WordTrace]
  refine ⟨90659176390911056986744483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120878901854548075982325977 90659176390911056986744483)
  ·
    refine ⟨135988764586366585480116725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90659176390911056986744483 135988764586366585480116725)
    ·
      refine ⟨12748946679971867388760943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 135988764586366585480116725 12748946679971867388760943)
      ·
        refine ⟨19123420019957801083141415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12748946679971867388760943 19123420019957801083141415)
        ·
          refine ⟨28685130029936701624712123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19123420019957801083141415 28685130029936701624712123)
          ·
            refine ⟨43027695044905052437068185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28685130029936701624712123 43027695044905052437068185)
            ·
              refine ⟨32270771283678789327801139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43027695044905052437068185 32270771283678789327801139)
              ·
                refine ⟨48406156925518183991701709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32270771283678789327801139 48406156925518183991701709)
                ·
                  refine ⟨18152308847069318996888141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48406156925518183991701709 18152308847069318996888141)
                  ·
                    refine ⟨6807115817650994623833053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18152308847069318996888141 6807115817650994623833053)
                    ·
                      refine ⟨2552668431619122983937395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6807115817650994623833053 2552668431619122983937395)
                      ·
                        rfl

theorem cell23_4971304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_4971304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4971304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4971304 prefixEnd_4971304 := by exact prefixLift 4971304
  have htrace : WordTrace (prefixWord ++ tailWord_4971304) baseStart_4971304 baseEnd_4971304 := by
    simpa [prefixWord, tailWord_4971304, baseEnd_4971304] using wordTrace_append hprefix tailTrace_4971304
  have hstable : (prefixWord ++ tailWord_4971304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4971304).length < 2 ^ (prefixWord ++ tailWord_4971304).sum := by decide
  have hdescent : baseEnd_4971304 < baseStart_4971304 := by decide
  rcases family_descends (prefixWord ++ tailWord_4971304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4971322 : List Nat := [3, 1, 1, 1, 6, 1, 3, 2, 1, 2, 2]
def baseStart_4971322 : Nat := 118140960795 + 4971322 * 2 ^ 59
def prefixEnd_4971322 : Nat := 4983230072969 + 3 ^ 40 * 4971322 * 2
def baseEnd_4971322 : Nat := 2552677674270903913512313

theorem tailTrace_4971322 : CollatzResearch.WordTrace tailWord_4971322 prefixEnd_4971322 2552677674270903913512313 := by
  unfold tailWord_4971322
  simp only [CollatzResearch.WordTrace]
  refine ⟨45329752323939225761911055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120879339530504602031762813 45329752323939225761911055)
  ·
    refine ⟨67994628485908838642866583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45329752323939225761911055 67994628485908838642866583)
    ·
      refine ⟨101991942728863257964299875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67994628485908838642866583 101991942728863257964299875)
      ·
        refine ⟨152987914093294886946449813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101991942728863257964299875 152987914093294886946449813)
        ·
          refine ⟨7171308473123197825614835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 152987914093294886946449813 7171308473123197825614835)
          ·
            refine ⟨10756962709684796738422253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7171308473123197825614835 10756962709684796738422253)
            ·
              refine ⟨4033861016131798776908345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10756962709684796738422253 4033861016131798776908345)
              ·
                refine ⟨3025395762098849082681259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4033861016131798776908345 3025395762098849082681259)
                ·
                  refine ⟨4538093643148273624021889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3025395762098849082681259 4538093643148273624021889)
                  ·
                    refine ⟨3403570232361205218016417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4538093643148273624021889 3403570232361205218016417)
                    ·
                      refine ⟨2552677674270903913512313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3403570232361205218016417 2552677674270903913512313)
                      ·
                        rfl

theorem cell23_4971322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 3, 2, 1, 2, 2].length) (baseStart_4971322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4971322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4971322 prefixEnd_4971322 := by exact prefixLift 4971322
  have htrace : WordTrace (prefixWord ++ tailWord_4971322) baseStart_4971322 baseEnd_4971322 := by
    simpa [prefixWord, tailWord_4971322, baseEnd_4971322] using wordTrace_append hprefix tailTrace_4971322
  have hstable : (prefixWord ++ tailWord_4971322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4971322).length < 2 ^ (prefixWord ++ tailWord_4971322).sum := by decide
  have hdescent : baseEnd_4971322 < baseStart_4971322 := by decide
  rcases family_descends (prefixWord ++ tailWord_4971322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4971332 : List Nat := [2, 3, 4, 2, 1, 2, 2, 1, 2, 4]
def baseStart_4971332 : Nat := 118140960795 + 4971332 * 2 ^ 59
def prefixEnd_4971332 : Nat := 4983230072969 + 3 ^ 40 * 4971332 * 2
def baseEnd_4971332 : Nat := 850894269692482958129089

theorem tailTrace_4971332 : CollatzResearch.WordTrace tailWord_4971332 prefixEnd_4971332 850894269692482958129089 := by
  unfold tailWord_4971332
  simp only [CollatzResearch.WordTrace]
  refine ⟨90659687012860337377754125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120879582683813783170338833 90659687012860337377754125)
  ·
    refine ⟨33997382629822626516657797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90659687012860337377754125 33997382629822626516657797)
    ·
      refine ⟨6374509243091742471873337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33997382629822626516657797 6374509243091742471873337)
      ·
        refine ⟨4780881932318806853905003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6374509243091742471873337 4780881932318806853905003)
        ·
          refine ⟨7171322898478210280857505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4780881932318806853905003 7171322898478210280857505)
          ·
            refine ⟨5378492173858657710643129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7171322898478210280857505 5378492173858657710643129)
            ·
              refine ⟨4033869130393993282982347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5378492173858657710643129 4033869130393993282982347)
              ·
                refine ⟨6050803695590989924473521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4033869130393993282982347 6050803695590989924473521)
                ·
                  refine ⟨4538102771693242443355141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6050803695590989924473521 4538102771693242443355141)
                  ·
                    refine ⟨850894269692482958129089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4538102771693242443355141 850894269692482958129089)
                    ·
                      rfl

theorem cell23_4971332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_4971332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4971332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4971332 prefixEnd_4971332 := by exact prefixLift 4971332
  have htrace : WordTrace (prefixWord ++ tailWord_4971332) baseStart_4971332 baseEnd_4971332 := by
    simpa [prefixWord, tailWord_4971332, baseEnd_4971332] using wordTrace_append hprefix tailTrace_4971332
  have hstable : (prefixWord ++ tailWord_4971332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4971332).length < 2 ^ (prefixWord ++ tailWord_4971332).sum := by decide
  have hdescent : baseEnd_4971332 < baseStart_4971332 := by decide
  rcases family_descends (prefixWord ++ tailWord_4971332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4971348 : List Nat := [2, 4, 1, 1, 4, 1, 1, 1, 3, 3, 2]
def baseStart_4971348 : Nat := 118140960795 + 4971348 * 2 ^ 59
def prefixEnd_4971348 : Nat := 4983230072969 + 3 ^ 40 * 4971348 * 2
def baseEnd_4971348 : Nat := 2552691024767920811787193

theorem tailTrace_4971348 : CollatzResearch.WordTrace tailWord_4971348 prefixEnd_4971348 2552691024767920811787193 := by
  unfold tailWord_4971348
  simp only [CollatzResearch.WordTrace]
  refine ⟨90659978796831354744045349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120879971729108472992060465 90659978796831354744045349)
  ·
    refine ⟨16998746024405879014508503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90659978796831354744045349 16998746024405879014508503)
    ·
      refine ⟨25498119036608818521762755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16998746024405879014508503 25498119036608818521762755)
      ·
        refine ⟨38247178554913227782644133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25498119036608818521762755 38247178554913227782644133)
        ·
          refine ⟨7171345979046230209245775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38247178554913227782644133 7171345979046230209245775)
          ·
            refine ⟨10757018968569345313868663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7171345979046230209245775 10757018968569345313868663)
            ·
              refine ⟨16135528452854017970802995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10757018968569345313868663 16135528452854017970802995)
              ·
                refine ⟨24203292679281026956204493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16135528452854017970802995 24203292679281026956204493)
                ·
                  refine ⟨9076234754730385108576685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24203292679281026956204493 9076234754730385108576685)
                  ·
                    refine ⟨3403588033023894415716257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9076234754730385108576685 3403588033023894415716257)
                    ·
                      refine ⟨2552691024767920811787193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3403588033023894415716257 2552691024767920811787193)
                      ·
                        rfl

theorem cell23_4971348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 3, 3, 2].length) (baseStart_4971348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4971348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4971348 prefixEnd_4971348 := by exact prefixLift 4971348
  have htrace : WordTrace (prefixWord ++ tailWord_4971348) baseStart_4971348 baseEnd_4971348 := by
    simpa [prefixWord, tailWord_4971348, baseEnd_4971348] using wordTrace_append hprefix tailTrace_4971348
  have hstable : (prefixWord ++ tailWord_4971348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4971348).length < 2 ^ (prefixWord ++ tailWord_4971348).sum := by decide
  have hdescent : baseEnd_4971348 < baseStart_4971348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4971348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4971361 : List Nat := [1, 2, 3, 1, 1, 1, 2, 4, 4, 2, 2]
def baseStart_4971361 : Nat := 118140960795 + 4971361 * 2 ^ 59
def prefixEnd_4971361 : Nat := 4983230072969 + 3 ^ 40 * 4971361 * 2
def baseEnd_4971361 : Nat := 2552697700016429260924633

theorem tailTrace_4971361 : CollatzResearch.WordTrace tailWord_4971361 prefixEnd_4971361 2552697700016429260924633 := by
  unfold tailWord_4971361
  simp only [CollatzResearch.WordTrace]
  refine ⟨181320431742615612708313937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120880287828410408472209291 181320431742615612708313937)
  ·
    refine ⟨135990323806961709531235453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181320431742615612708313937 135990323806961709531235453)
    ·
      refine ⟨50996371427610641074213295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135990323806961709531235453 50996371427610641074213295)
      ·
        refine ⟨76494557141415961611319943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50996371427610641074213295 76494557141415961611319943)
        ·
          refine ⟨114741835712123942416979915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76494557141415961611319943 114741835712123942416979915)
          ·
            refine ⟨172112753568185913625469873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114741835712123942416979915 172112753568185913625469873)
            ·
              refine ⟨129084565176139435219102405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 172112753568185913625469873 129084565176139435219102405)
              ·
                refine ⟨24203355970526144103581701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 129084565176139435219102405 24203355970526144103581701)
                ·
                  refine ⟨4538129244473652019421569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24203355970526144103581701 4538129244473652019421569)
                  ·
                    refine ⟨3403596933355239014566177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4538129244473652019421569 3403596933355239014566177)
                    ·
                      refine ⟨2552697700016429260924633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3403596933355239014566177 2552697700016429260924633)
                      ·
                        rfl

theorem cell23_4971361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 4, 2, 2].length) (baseStart_4971361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4971361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4971361 prefixEnd_4971361 := by exact prefixLift 4971361
  have htrace : WordTrace (prefixWord ++ tailWord_4971361) baseStart_4971361 baseEnd_4971361 := by
    simpa [prefixWord, tailWord_4971361, baseEnd_4971361] using wordTrace_append hprefix tailTrace_4971361
  have hstable : (prefixWord ++ tailWord_4971361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4971361).length < 2 ^ (prefixWord ++ tailWord_4971361).sum := by decide
  have hdescent : baseEnd_4971361 < baseStart_4971361 := by decide
  rcases family_descends (prefixWord ++ tailWord_4971361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4971364 : List Nat := [2, 3, 1, 1, 4, 1, 2, 1, 2, 1, 5]
def baseStart_4971364 : Nat := 118140960795 + 4971364 * 2 ^ 59
def prefixEnd_4971364 : Nat := 4983230072969 + 3 ^ 40 * 4971364 * 2
def baseEnd_4971364 : Nat := 2552699240458392749187119

theorem tailTrace_4971364 : CollatzResearch.WordTrace tailWord_4971364 prefixEnd_4971364 2552699240458392749187119 := by
  unfold tailWord_4971364
  simp only [CollatzResearch.WordTrace]
  refine ⟨90660270580802372110336573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120880360774403162813782097 90660270580802372110336573)
  ·
    refine ⟨33997601467800889541376215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90660270580802372110336573 33997601467800889541376215)
    ·
      refine ⟨50996402201701334312064323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33997601467800889541376215 50996402201701334312064323)
      ·
        refine ⟨76494603302552001468096485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50996402201701334312064323 76494603302552001468096485)
        ·
          refine ⟨14342738119228500275268091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76494603302552001468096485 14342738119228500275268091)
          ·
            refine ⟨21514107178842750412902137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14342738119228500275268091 21514107178842750412902137)
            ·
              refine ⟨16135580384132062809676603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21514107178842750412902137 16135580384132062809676603)
              ·
                refine ⟨24203370576198094214514905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16135580384132062809676603 24203370576198094214514905)
                ·
                  refine ⟨18152527932148570660886179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24203370576198094214514905 18152527932148570660886179)
                  ·
                    refine ⟨27228791898222855991329269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18152527932148570660886179 27228791898222855991329269)
                    ·
                      refine ⟨2552699240458392749187119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27228791898222855991329269 2552699240458392749187119)
                      ·
                        rfl

theorem cell23_4971364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 2, 1, 5].length) (baseStart_4971364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4971364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4971364 prefixEnd_4971364 := by exact prefixLift 4971364
  have htrace : WordTrace (prefixWord ++ tailWord_4971364) baseStart_4971364 baseEnd_4971364 := by
    simpa [prefixWord, tailWord_4971364, baseEnd_4971364] using wordTrace_append hprefix tailTrace_4971364
  have hstable : (prefixWord ++ tailWord_4971364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4971364).length < 2 ^ (prefixWord ++ tailWord_4971364).sum := by decide
  have hdescent : baseEnd_4971364 < baseStart_4971364 := by decide
  rcases family_descends (prefixWord ++ tailWord_4971364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4971378 : List Nat := [3, 2, 1, 2, 1, 1, 3, 4, 2, 2, 2]
def baseStart_4971378 : Nat := 118140960795 + 4971378 * 2 ^ 59
def prefixEnd_4971378 : Nat := 4983230072969 + 3 ^ 40 * 4971378 * 2
def baseEnd_4971378 : Nat := 2552706429187555694412055

theorem tailTrace_4971378 : CollatzResearch.WordTrace tailWord_4971378 prefixEnd_4971378 2552706429187555694412055 := by
  unfold tailWord_4971378
  simp only [CollatzResearch.WordTrace]
  refine ⟨45330262945888506152920697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120880701189036016407788525 45330262945888506152920697)
  ·
    refine ⟨33997697209416379614690523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45330262945888506152920697 33997697209416379614690523)
    ·
      refine ⟨50996545814124569422035785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33997697209416379614690523 50996545814124569422035785)
      ·
        refine ⟨38247409360593427066526839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50996545814124569422035785 38247409360593427066526839)
        ·
          refine ⟨57371114040890140599790259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38247409360593427066526839 57371114040890140599790259)
          ·
            refine ⟨86056671061335210899685389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57371114040890140599790259 86056671061335210899685389)
            ·
              refine ⟨32271251648000704087382021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86056671061335210899685389 32271251648000704087382021)
              ·
                refine ⟨6050859684000132016384129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32271251648000704087382021 6050859684000132016384129)
                ·
                  refine ⟨4538144763000099012288097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6050859684000132016384129 4538144763000099012288097)
                  ·
                    refine ⟨3403608572250074259216073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4538144763000099012288097 3403608572250074259216073)
                    ·
                      refine ⟨2552706429187555694412055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3403608572250074259216073 2552706429187555694412055)
                      ·
                        rfl

theorem cell23_4971378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 4, 2, 2, 2].length) (baseStart_4971378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4971378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4971378 prefixEnd_4971378 := by exact prefixLift 4971378
  have htrace : WordTrace (prefixWord ++ tailWord_4971378) baseStart_4971378 baseEnd_4971378 := by
    simpa [prefixWord, tailWord_4971378, baseEnd_4971378] using wordTrace_append hprefix tailTrace_4971378
  have hstable : (prefixWord ++ tailWord_4971378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4971378).length < 2 ^ (prefixWord ++ tailWord_4971378).sum := by decide
  have hdescent : baseEnd_4971378 < baseStart_4971378 := by decide
  rcases family_descends (prefixWord ++ tailWord_4971378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4971418 : List Nat := [3, 1, 1, 4, 3, 1, 2, 3, 5]
def baseStart_4971418 : Nat := 118140960795 + 4971418 * 2 ^ 59
def prefixEnd_4971418 : Nat := 4983230072969 + 3 ^ 40 * 4971418 * 2
def baseEnd_4971418 : Nat := 283636329823748393101319

theorem tailTrace_4971418 : CollatzResearch.WordTrace tailWord_4971418 prefixEnd_4971418 283636329823748393101319 := by
  unfold tailWord_4971418
  simp only [CollatzResearch.WordTrace]
  refine ⟨45330627675852277860784727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120881673802272740962092605 45330627675852277860784727)
  ·
    refine ⟨67995941513778416791177091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45330627675852277860784727 67995941513778416791177091)
    ·
      refine ⟨101993912270667625186765637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67995941513778416791177091 101993912270667625186765637)
      ·
        refine ⟨19123858550750179722518557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101993912270667625186765637 19123858550750179722518557)
        ·
          refine ⟨7171446956531317395944459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19123858550750179722518557 7171446956531317395944459)
          ·
            refine ⟨10757170434796976093916689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7171446956531317395944459 10757170434796976093916689)
            ·
              refine ⟨8067877826097732070437517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10757170434796976093916689 8067877826097732070437517)
              ·
                refine ⟨3025454184786649526414069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8067877826097732070437517 3025454184786649526414069)
                ·
                  refine ⟨283636329823748393101319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3025454184786649526414069 283636329823748393101319)
                  ·
                    rfl

theorem cell23_4971418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 3, 5].length) (baseStart_4971418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4971418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4971418 prefixEnd_4971418 := by exact prefixLift 4971418
  have htrace : WordTrace (prefixWord ++ tailWord_4971418) baseStart_4971418 baseEnd_4971418 := by
    simpa [prefixWord, tailWord_4971418, baseEnd_4971418] using wordTrace_append hprefix tailTrace_4971418
  have hstable : (prefixWord ++ tailWord_4971418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4971418).length < 2 ^ (prefixWord ++ tailWord_4971418).sum := by decide
  have hdescent : baseEnd_4971418 < baseStart_4971418 := by decide
  rcases family_descends (prefixWord ++ tailWord_4971418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4971446 : List Nat := [5, 1, 4, 1, 2, 1, 1, 1, 1, 4, 2]
def baseStart_4971446 : Nat := 118140960795 + 4971446 * 2 ^ 59
def prefixEnd_4971446 : Nat := 4983230072969 + 3 ^ 40 * 4971446 * 2
def baseEnd_4971446 : Nat := 2552741345872061428361743

theorem tailTrace_4971446 : CollatzResearch.WordTrace tailWord_4971446 prefixEnd_4971446 2552741345872061428361743 := by
  unfold tailWord_4971446
  simp only [CollatzResearch.WordTrace]
  refine ⟨11332720746706729514072387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 120882354631538448150105461 11332720746706729514072387)
  ·
    refine ⟨16999081120060094271108581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11332720746706729514072387 16999081120060094271108581)
    ·
      refine ⟨3187327710011267675832859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16999081120060094271108581 3187327710011267675832859)
      ·
        refine ⟨4780991565016901513749289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3187327710011267675832859 4780991565016901513749289)
        ·
          refine ⟨3585743673762676135311967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4780991565016901513749289 3585743673762676135311967)
          ·
            refine ⟨5378615510644014202967951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3585743673762676135311967 5378615510644014202967951)
            ·
              refine ⟨8067923265966021304451927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5378615510644014202967951 8067923265966021304451927)
              ·
                refine ⟨12101884898949031956677891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8067923265966021304451927 12101884898949031956677891)
                ·
                  refine ⟨18152827348423547935016837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12101884898949031956677891 18152827348423547935016837)
                  ·
                    refine ⟨3403655127829415237815657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18152827348423547935016837 3403655127829415237815657)
                    ·
                      refine ⟨2552741345872061428361743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3403655127829415237815657 2552741345872061428361743)
                      ·
                        rfl

theorem cell23_4971446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_4971446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4971446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4971446 prefixEnd_4971446 := by exact prefixLift 4971446
  have htrace : WordTrace (prefixWord ++ tailWord_4971446) baseStart_4971446 baseEnd_4971446 := by
    simpa [prefixWord, tailWord_4971446, baseEnd_4971446] using wordTrace_append hprefix tailTrace_4971446
  have hstable : (prefixWord ++ tailWord_4971446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4971446).length < 2 ^ (prefixWord ++ tailWord_4971446).sum := by decide
  have hdescent : baseEnd_4971446 < baseStart_4971446 := by decide
  rcases family_descends (prefixWord ++ tailWord_4971446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4971469 : List Nat := [1, 6, 3, 1, 1, 2, 1, 3, 5]
def baseStart_4971469 : Nat := 118140960795 + 4971469 * 2 ^ 59
def prefixEnd_4971469 : Nat := 4983230072969 + 3 ^ 40 * 4971469 * 2
def baseEnd_4971469 : Nat := 283639239547457204263793

theorem tailTrace_4971469 : CollatzResearch.WordTrace tailWord_4971469 prefixEnd_4971469 283639239547457204263793 := by
  unfold tailWord_4971469
  simp only [CollatzResearch.WordTrace]
  refine ⟨181324370826224347153245461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120882913884149564768830307 181324370826224347153245461)
  ·
    refine ⟨8499579882479266272808381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 181324370826224347153245461 8499579882479266272808381)
    ·
      refine ⟨3187342455929724852303143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8499579882479266272808381 3187342455929724852303143)
      ·
        refine ⟨4781013683894587278454715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3187342455929724852303143 4781013683894587278454715)
        ·
          refine ⟨7171520525841880917682073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4781013683894587278454715 7171520525841880917682073)
          ·
            refine ⟨5378640394381410688261555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7171520525841880917682073 5378640394381410688261555)
            ·
              refine ⟨8067960591572116032392333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5378640394381410688261555 8067960591572116032392333)
              ·
                refine ⟨3025485221839543512147125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8067960591572116032392333 3025485221839543512147125)
                ·
                  refine ⟨283639239547457204263793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3025485221839543512147125 283639239547457204263793)
                  ·
                    rfl

theorem cell23_4971469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_4971469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4971469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4971469 prefixEnd_4971469 := by exact prefixLift 4971469
  have htrace : WordTrace (prefixWord ++ tailWord_4971469) baseStart_4971469 baseEnd_4971469 := by
    simpa [prefixWord, tailWord_4971469, baseEnd_4971469] using wordTrace_append hprefix tailTrace_4971469
  have hstable : (prefixWord ++ tailWord_4971469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4971469).length < 2 ^ (prefixWord ++ tailWord_4971469).sum := by decide
  have hdescent : baseEnd_4971469 < baseStart_4971469 := by decide
  rcases family_descends (prefixWord ++ tailWord_4971469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4971504 : List Nat := [2, 1, 1, 1, 3, 2, 1, 4, 3, 5]
def baseStart_4971504 : Nat := 118140960795 + 4971504 * 2 ^ 59
def prefixEnd_4971504 : Nat := 4983230072969 + 3 ^ 40 * 4971504 * 2
def baseEnd_4971504 : Nat := 850923709250007400478825

theorem tailTrace_4971504 : CollatzResearch.WordTrace tailWord_4971504 prefixEnd_4971504 850923709250007400478825 := by
  unfold tailWord_4971504
  simp only [CollatzResearch.WordTrace]
  refine ⟨90662823690548774065384783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120883764920731698753846377 90662823690548774065384783)
  ·
    refine ⟨135994235535823161098077175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90662823690548774065384783 135994235535823161098077175)
    ·
      refine ⟨203991353303734741647115763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135994235535823161098077175 203991353303734741647115763)
      ·
        refine ⟨305987029955602112470673645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203991353303734741647115763 305987029955602112470673645)
        ·
          refine ⟨114745136233350792176502617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 305987029955602112470673645 114745136233350792176502617)
          ·
            refine ⟨86058852175013094132376963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114745136233350792176502617 86058852175013094132376963)
            ·
              refine ⟨129088278262519641198565445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86058852175013094132376963 129088278262519641198565445)
              ·
                refine ⟨24204052174222432724731021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 129088278262519641198565445 24204052174222432724731021)
                ·
                  refine ⟨9076519565333412271774133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24204052174222432724731021 9076519565333412271774133)
                  ·
                    refine ⟨850923709250007400478825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9076519565333412271774133 850923709250007400478825)
                    ·
                      rfl

theorem cell23_4971504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 3, 5].length) (baseStart_4971504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4971504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4971504 prefixEnd_4971504 := by exact prefixLift 4971504
  have htrace : WordTrace (prefixWord ++ tailWord_4971504) baseStart_4971504 baseEnd_4971504 := by
    simpa [prefixWord, tailWord_4971504, baseEnd_4971504] using wordTrace_append hprefix tailTrace_4971504
  have hstable : (prefixWord ++ tailWord_4971504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4971504).length < 2 ^ (prefixWord ++ tailWord_4971504).sum := by decide
  have hdescent : baseEnd_4971504 < baseStart_4971504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4971504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4971521 : List Nat := [1, 2, 4, 1, 2, 3, 1, 1, 3, 5]
def baseStart_4971521 : Nat := 118140960795 + 4971521 * 2 ^ 59
def prefixEnd_4971521 : Nat := 4983230072969 + 3 ^ 40 * 4971521 * 2
def baseEnd_4971521 : Nat := 850926618973716211641299

theorem tailTrace_4971521 : CollatzResearch.WordTrace tailWord_4971521 prefixEnd_4971521 850926618973716211641299 := by
  unfold tailWord_4971521
  simp only [CollatzResearch.WordTrace]
  refine ⟨181326267422035960034138417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120884178281357306689425611 181326267422035960034138417)
  ·
    refine ⟨135994700566526970025603813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181326267422035960034138417 135994700566526970025603813)
    ·
      refine ⟨25499006356223806879800715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 135994700566526970025603813 25499006356223806879800715)
      ·
        refine ⟨38248509534335710319701073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25499006356223806879800715 38248509534335710319701073)
        ·
          refine ⟨28686382150751782739775805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38248509534335710319701073 28686382150751782739775805)
          ·
            refine ⟨10757393306531918527415927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28686382150751782739775805 10757393306531918527415927)
            ·
              refine ⟨16136089959797877791123891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10757393306531918527415927 16136089959797877791123891)
              ·
                refine ⟨24204134939696816686685837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16136089959797877791123891 24204134939696816686685837)
                ·
                  refine ⟨9076550602386306257507189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24204134939696816686685837 9076550602386306257507189)
                  ·
                    refine ⟨850926618973716211641299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9076550602386306257507189 850926618973716211641299)
                    ·
                      rfl

theorem cell23_4971521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_4971521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4971521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4971521 prefixEnd_4971521 := by exact prefixLift 4971521
  have htrace : WordTrace (prefixWord ++ tailWord_4971521) baseStart_4971521 baseEnd_4971521 := by
    simpa [prefixWord, tailWord_4971521, baseEnd_4971521] using wordTrace_append hprefix tailTrace_4971521
  have hstable : (prefixWord ++ tailWord_4971521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4971521).length < 2 ^ (prefixWord ++ tailWord_4971521).sum := by decide
  have hdescent : baseEnd_4971521 < baseStart_4971521 := by decide
  rcases family_descends (prefixWord ++ tailWord_4971521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4971522 : List Nat := [3, 4, 1, 3, 1, 1, 2, 1, 2, 2, 3]
def baseStart_4971522 : Nat := 118140960795 + 4971522 * 2 ^ 59
def prefixEnd_4971522 : Nat := 4983230072969 + 3 ^ 40 * 4971522 * 2
def baseEnd_4971522 : Nat := 2552780370401803131011393

theorem tailTrace_4971522 : CollatzResearch.WordTrace tailWord_4971522 prefixEnd_4971522 2552780370401803131011393 := by
  unfold tailWord_4971522
  simp only [CollatzResearch.WordTrace]
  refine ⟨45331575973758084301231205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120884202596688224803283213 45331575973758084301231205)
  ·
    refine ⟨8499670495079640806480851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45331575973758084301231205 8499670495079640806480851)
    ·
      refine ⟨12749505742619461209721277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8499670495079640806480851 12749505742619461209721277)
      ·
        refine ⟨4781064653482297953645479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12749505742619461209721277 4781064653482297953645479)
        ·
          refine ⟨7171596980223446930468219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4781064653482297953645479 7171596980223446930468219)
          ·
            refine ⟨10757395470335170395702329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7171596980223446930468219 10757395470335170395702329)
            ·
              refine ⟨8068046602751377796776747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10757395470335170395702329 8068046602751377796776747)
              ·
                refine ⟨12102069904127066695165121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8068046602751377796776747 12102069904127066695165121)
                ·
                  refine ⟨9076552428095300021373841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12102069904127066695165121 9076552428095300021373841)
                  ·
                    refine ⟨6807414321071475016030381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9076552428095300021373841 6807414321071475016030381)
                    ·
                      refine ⟨2552780370401803131011393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6807414321071475016030381 2552780370401803131011393)
                      ·
                        rfl

theorem cell23_4971522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_4971522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4971522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4971522 prefixEnd_4971522 := by exact prefixLift 4971522
  have htrace : WordTrace (prefixWord ++ tailWord_4971522) baseStart_4971522 baseEnd_4971522 := by
    simpa [prefixWord, tailWord_4971522, baseEnd_4971522] using wordTrace_append hprefix tailTrace_4971522
  have hstable : (prefixWord ++ tailWord_4971522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4971522).length < 2 ^ (prefixWord ++ tailWord_4971522).sum := by decide
  have hdescent : baseEnd_4971522 < baseStart_4971522 := by decide
  rcases family_descends (prefixWord ++ tailWord_4971522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4971528 : List Nat := [2, 1, 3, 2, 1, 3, 1, 3, 2, 3, 2]
def baseStart_4971528 : Nat := 118140960795 + 4971528 * 2 ^ 59
def prefixEnd_4971528 : Nat := 4983230072969 + 3 ^ 40 * 4971528 * 2
def baseEnd_4971528 : Nat := 2552783451285730107536365

theorem tailTrace_4971528 : CollatzResearch.WordTrace tailWord_4971528 prefixEnd_4971528 2552783451285730107536365 := by
  unfold tailWord_4971528
  simp only [CollatzResearch.WordTrace]
  refine ⟨90663261366505300114821619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120884348488673733486428825 90663261366505300114821619)
  ·
    refine ⟨135994892049757950172232429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90663261366505300114821619 135994892049757950172232429)
    ·
      refine ⟨50998084518659231314587161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135994892049757950172232429 50998084518659231314587161)
      ·
        refine ⟨38248563388994423485940371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50998084518659231314587161 38248563388994423485940371)
        ·
          refine ⟨57372845083491635228910557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38248563388994423485940371 57372845083491635228910557)
          ·
            refine ⟨21514816906309363210841459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57372845083491635228910557 21514816906309363210841459)
            ·
              refine ⟨32272225359464044816262189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21514816906309363210841459 32272225359464044816262189)
              ·
                refine ⟨12102084509799016806098321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32272225359464044816262189 12102084509799016806098321)
                ·
                  refine ⟨9076563382349262604573741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12102084509799016806098321 9076563382349262604573741)
                  ·
                    refine ⟨3403711268380973476715153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9076563382349262604573741 3403711268380973476715153)
                    ·
                      refine ⟨2552783451285730107536365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3403711268380973476715153 2552783451285730107536365)
                      ·
                        rfl

theorem cell23_4971528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 3, 2, 3, 2].length) (baseStart_4971528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4971528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4971528 prefixEnd_4971528 := by exact prefixLift 4971528
  have htrace : WordTrace (prefixWord ++ tailWord_4971528) baseStart_4971528 baseEnd_4971528 := by
    simpa [prefixWord, tailWord_4971528, baseEnd_4971528] using wordTrace_append hprefix tailTrace_4971528
  have hstable : (prefixWord ++ tailWord_4971528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4971528).length < 2 ^ (prefixWord ++ tailWord_4971528).sum := by decide
  have hdescent : baseEnd_4971528 < baseStart_4971528 := by decide
  rcases family_descends (prefixWord ++ tailWord_4971528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4971592 : List Nat := [2, 1, 3, 1, 1, 1, 6, 3, 1, 2, 2]
def baseStart_4971592 : Nat := 118140960795 + 4971592 * 2 ^ 59
def prefixEnd_4971592 : Nat := 4983230072969 + 3 ^ 40 * 4971592 * 2
def baseEnd_4971592 : Nat := 2552816314047617857136071

theorem tailTrace_4971592 : CollatzResearch.WordTrace tailWord_4971592 prefixEnd_4971592 2552816314047617857136071 := by
  unfold tailWord_4971592
  simp only [CollatzResearch.WordTrace]
  refine ⟨90664428502389369579986515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120885904669852492773315353 90664428502389369579986515)
  ·
    refine ⟨135996642753584054369979773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90664428502389369579986515 135996642753584054369979773)
    ·
      refine ⟨50998741032594020388742415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135996642753584054369979773 50998741032594020388742415)
      ·
        refine ⟨76498111548891030583113623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50998741032594020388742415 76498111548891030583113623)
        ·
          refine ⟨114747167323336545874670435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76498111548891030583113623 114747167323336545874670435)
          ·
            refine ⟨172120750985004818812005653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114747167323336545874670435 172120750985004818812005653)
            ·
              refine ⟨8068160202422100881812765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 172120750985004818812005653 8068160202422100881812765)
              ·
                refine ⟨3025560075908287830679787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8068160202422100881812765 3025560075908287830679787)
                ·
                  refine ⟨4538340113862431746019681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3025560075908287830679787 4538340113862431746019681)
                  ·
                    refine ⟨3403755085396823809514761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4538340113862431746019681 3403755085396823809514761)
                    ·
                      refine ⟨2552816314047617857136071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3403755085396823809514761 2552816314047617857136071)
                      ·
                        rfl

theorem cell23_4971592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 3, 1, 2, 2].length) (baseStart_4971592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4971592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4971592 prefixEnd_4971592 := by exact prefixLift 4971592
  have htrace : WordTrace (prefixWord ++ tailWord_4971592) baseStart_4971592 baseEnd_4971592 := by
    simpa [prefixWord, tailWord_4971592, baseEnd_4971592] using wordTrace_append hprefix tailTrace_4971592
  have hstable : (prefixWord ++ tailWord_4971592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4971592).length < 2 ^ (prefixWord ++ tailWord_4971592).sum := by decide
  have hdescent : baseEnd_4971592 < baseStart_4971592 := by decide
  rcases family_descends (prefixWord ++ tailWord_4971592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4971608 : List Nat := [2, 1, 2, 2, 1, 3, 3, 1, 4, 1, 3]
def baseStart_4971608 : Nat := 118140960795 + 4971608 * 2 ^ 59
def prefixEnd_4971608 : Nat := 4983230072969 + 3 ^ 40 * 4971608 * 2
def baseEnd_4971608 : Nat := 2552824529738089794535997

theorem tailTrace_4971608 : CollatzResearch.WordTrace tailWord_4971608 prefixEnd_4971608 2552824529738089794535997 := by
  unfold tailWord_4971608
  simp only [CollatzResearch.WordTrace]
  refine ⟨90664720286360386946277739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120886293715147182595036985 90664720286360386946277739)
  ·
    refine ⟨135997080429540580419416609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90664720286360386946277739 135997080429540580419416609)
    ·
      refine ⟨101997810322155435314562457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135997080429540580419416609 101997810322155435314562457)
      ·
        refine ⟨76498357741616576485921843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101997810322155435314562457 76498357741616576485921843)
        ·
          refine ⟨114747536612424864728882765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76498357741616576485921843 114747536612424864728882765)
          ·
            refine ⟨43030326229659324273331037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114747536612424864728882765 43030326229659324273331037)
            ·
              refine ⟨16136372336122246602499139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43030326229659324273331037 16136372336122246602499139)
              ·
                refine ⟨24204558504183369903748709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16136372336122246602499139 24204558504183369903748709)
                ·
                  refine ⟨4538354719534381856952883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24204558504183369903748709 4538354719534381856952883)
                  ·
                    refine ⟨6807532079301572785429325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4538354719534381856952883 6807532079301572785429325)
                    ·
                      refine ⟨2552824529738089794535997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6807532079301572785429325 2552824529738089794535997)
                      ·
                        rfl

theorem cell23_4971608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 4, 1, 3].length) (baseStart_4971608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4971608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4971608 prefixEnd_4971608 := by exact prefixLift 4971608
  have htrace : WordTrace (prefixWord ++ tailWord_4971608) baseStart_4971608 baseEnd_4971608 := by
    simpa [prefixWord, tailWord_4971608, baseEnd_4971608] using wordTrace_append hprefix tailTrace_4971608
  have hstable : (prefixWord ++ tailWord_4971608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4971608).length < 2 ^ (prefixWord ++ tailWord_4971608).sum := by decide
  have hdescent : baseEnd_4971608 < baseStart_4971608 := by decide
  rcases family_descends (prefixWord ++ tailWord_4971608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4971648 : List Nat := [2, 1, 1, 2, 1, 3, 2, 4, 1, 4, 2]
def baseStart_4971648 : Nat := 118140960795 + 4971648 * 2 ^ 59
def prefixEnd_4971648 : Nat := 4983230072969 + 3 ^ 40 * 4971648 * 2
def baseEnd_4971648 : Nat := 2552845068964269638035813

theorem tailTrace_4971648 : CollatzResearch.WordTrace tailWord_4971648 prefixEnd_4971648 2552845068964269638035813 := by
  unfold tailWord_4971648
  simp only [CollatzResearch.WordTrace]
  refine ⟨90665449746287930362005799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120887266328383907149341065 90665449746287930362005799)
  ·
    refine ⟨135998174619431895543008699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90665449746287930362005799 135998174619431895543008699)
    ·
      refine ⟨203997261929147843314513049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135998174619431895543008699 203997261929147843314513049)
      ·
        refine ⟨152997946446860882485884787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203997261929147843314513049 152997946446860882485884787)
        ·
          refine ⟨229496919670291323728827181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152997946446860882485884787 229496919670291323728827181)
          ·
            refine ⟨86061344876359246398310193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 229496919670291323728827181 86061344876359246398310193)
            ·
              refine ⟨64546008657269434798732645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86061344876359246398310193 64546008657269434798732645)
              ·
                refine ⟨12102376623238019024762371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64546008657269434798732645 12102376623238019024762371)
                ·
                  refine ⟨18153564934857028537143557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12102376623238019024762371 18153564934857028537143557)
                  ·
                    refine ⟨3403793425285692850714417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18153564934857028537143557 3403793425285692850714417)
                    ·
                      refine ⟨2552845068964269638035813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3403793425285692850714417 2552845068964269638035813)
                      ·
                        rfl

theorem cell23_4971648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 4, 1, 4, 2].length) (baseStart_4971648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4971648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4971648 prefixEnd_4971648 := by exact prefixLift 4971648
  have htrace : WordTrace (prefixWord ++ tailWord_4971648) baseStart_4971648 baseEnd_4971648 := by
    simpa [prefixWord, tailWord_4971648, baseEnd_4971648] using wordTrace_append hprefix tailTrace_4971648
  have hstable : (prefixWord ++ tailWord_4971648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4971648).length < 2 ^ (prefixWord ++ tailWord_4971648).sum := by decide
  have hdescent : baseEnd_4971648 < baseStart_4971648 := by decide
  rcases family_descends (prefixWord ++ tailWord_4971648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4971651 : List Nat := [1, 1, 1, 3, 3, 2, 3, 1, 2, 1, 5]
def baseStart_4971651 : Nat := 118140960795 + 4971651 * 2 ^ 59
def prefixEnd_4971651 : Nat := 4983230072969 + 3 ^ 40 * 4971651 * 2
def baseEnd_4971651 : Nat := 2552846609406233126298299

theorem tailTrace_4971651 : CollatzResearch.WordTrace tailWord_4971651 prefixEnd_4971651 2552846609406233126298299 := by
  unfold tailWord_4971651
  simp only [CollatzResearch.WordTrace]
  refine ⟨181331008911564992236370807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120887339274376661490913871 181331008911564992236370807)
  ·
    refine ⟨271996513367347488354556211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181331008911564992236370807 271996513367347488354556211)
    ·
      refine ⟨407994770051021232531834317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271996513367347488354556211 407994770051021232531834317)
      ·
        refine ⟨152998038769132962199437869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 407994770051021232531834317 152998038769132962199437869)
        ·
          refine ⟨57374264538424860824789201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152998038769132962199437869 57374264538424860824789201)
          ·
            refine ⟨43030698403818645618591901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57374264538424860824789201 43030698403818645618591901)
            ·
              refine ⟨16136511901431992106971963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43030698403818645618591901 16136511901431992106971963)
              ·
                refine ⟨24204767852147988160457945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16136511901431992106971963 24204767852147988160457945)
                ·
                  refine ⟨18153575889110991120343459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24204767852147988160457945 18153575889110991120343459)
                  ·
                    refine ⟨27230363833666486680515189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18153575889110991120343459 27230363833666486680515189)
                    ·
                      refine ⟨2552846609406233126298299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27230363833666486680515189 2552846609406233126298299)
                      ·
                        rfl

theorem cell23_4971651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 2, 1, 5].length) (baseStart_4971651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4971651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4971651 prefixEnd_4971651 := by exact prefixLift 4971651
  have htrace : WordTrace (prefixWord ++ tailWord_4971651) baseStart_4971651 baseEnd_4971651 := by
    simpa [prefixWord, tailWord_4971651, baseEnd_4971651] using wordTrace_append hprefix tailTrace_4971651
  have hstable : (prefixWord ++ tailWord_4971651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4971651).length < 2 ^ (prefixWord ++ tailWord_4971651).sum := by decide
  have hdescent : baseEnd_4971651 < baseStart_4971651 := by decide
  rcases family_descends (prefixWord ++ tailWord_4971651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4971711 : List Nat := [1, 1, 2, 2, 2, 2, 3, 2, 1, 2, 5]
def baseStart_4971711 : Nat := 118140960795 + 4971711 * 2 ^ 59
def prefixEnd_4971711 : Nat := 4983230072969 + 3 ^ 40 * 4971711 * 2
def baseEnd_4971711 : Nat := 2552877418245502891548023

theorem tailTrace_4971711 : CollatzResearch.WordTrace tailWord_4971711 prefixEnd_4971711 2552877418245502891548023 := by
  unfold tailWord_4971711
  simp only [CollatzResearch.WordTrace]
  refine ⟨181333197291347622483554987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120888798194231748322369991 181333197291347622483554987)
  ·
    refine ⟨271999795937021433725332481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181333197291347622483554987 271999795937021433725332481)
    ·
      refine ⟨203999846952766075293999361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 271999795937021433725332481 203999846952766075293999361)
      ·
        refine ⟨152999885214574556470499521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203999846952766075293999361 152999885214574556470499521)
        ·
          refine ⟨114749913910930917352874641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152999885214574556470499521 114749913910930917352874641)
          ·
            refine ⟨86062435433198188014655981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114749913910930917352874641 86062435433198188014655981)
            ·
              refine ⟨32273413287449320505495993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86062435433198188014655981 32273413287449320505495993)
              ·
                refine ⟨24205059965586990379121995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32273413287449320505495993 24205059965586990379121995)
                ·
                  refine ⟨36307589948380485568682993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24205059965586990379121995 36307589948380485568682993)
                  ·
                    refine ⟨27230692461285364176512245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36307589948380485568682993 27230692461285364176512245)
                    ·
                      refine ⟨2552877418245502891548023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27230692461285364176512245 2552877418245502891548023)
                      ·
                        rfl

theorem cell23_4971711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 2, 5].length) (baseStart_4971711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4971711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4971711 prefixEnd_4971711 := by exact prefixLift 4971711
  have htrace : WordTrace (prefixWord ++ tailWord_4971711) baseStart_4971711 baseEnd_4971711 := by
    simpa [prefixWord, tailWord_4971711, baseEnd_4971711] using wordTrace_append hprefix tailTrace_4971711
  have hstable : (prefixWord ++ tailWord_4971711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4971711).length < 2 ^ (prefixWord ++ tailWord_4971711).sum := by decide
  have hdescent : baseEnd_4971711 < baseStart_4971711 := by decide
  rcases family_descends (prefixWord ++ tailWord_4971711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4971722 : List Nat := [3, 1, 2, 1, 3, 4, 2, 2, 5]
def baseStart_4971722 : Nat := 118140960795 + 4971722 * 2 ^ 59
def prefixEnd_4971722 : Nat := 4983230072969 + 3 ^ 40 * 4971722 * 2
def baseEnd_4971722 : Nat := 283653674059189149834497

theorem tailTrace_4971722 : CollatzResearch.WordTrace tailWord_4971722 prefixEnd_4971722 283653674059189149834497 := by
  unfold tailWord_4971722
  simp only [CollatzResearch.WordTrace]
  refine ⟨45333399623576942840551355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120889065662871847574803613 45333399623576942840551355)
  ·
    refine ⟨68000099435365414260827033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45333399623576942840551355 68000099435365414260827033)
    ·
      refine ⟨51000074576524060695620275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68000099435365414260827033 51000074576524060695620275)
      ·
        refine ⟨76500111864786091043430413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51000074576524060695620275 76500111864786091043430413)
        ·
          refine ⟨28687541949294784141286405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76500111864786091043430413 28687541949294784141286405)
          ·
            refine ⟨5378914115492772026491201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28687541949294784141286405 5378914115492772026491201)
            ·
              refine ⟨4034185586619579019868401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5378914115492772026491201 4034185586619579019868401)
              ·
                refine ⟨3025639189964684264901301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4034185586619579019868401 3025639189964684264901301)
                ·
                  refine ⟨283653674059189149834497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3025639189964684264901301 283653674059189149834497)
                  ·
                    rfl

theorem cell23_4971722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 2, 2, 5].length) (baseStart_4971722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4971722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4971722 prefixEnd_4971722 := by exact prefixLift 4971722
  have htrace : WordTrace (prefixWord ++ tailWord_4971722) baseStart_4971722 baseEnd_4971722 := by
    simpa [prefixWord, tailWord_4971722, baseEnd_4971722] using wordTrace_append hprefix tailTrace_4971722
  have hstable : (prefixWord ++ tailWord_4971722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4971722).length < 2 ^ (prefixWord ++ tailWord_4971722).sum := by decide
  have hdescent : baseEnd_4971722 < baseStart_4971722 := by decide
  rcases family_descends (prefixWord ++ tailWord_4971722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4971732 : List Nat := [2, 4, 1, 4, 1, 1, 1, 1, 2, 3, 3]
def baseStart_4971732 : Nat := 118140960795 + 4971732 * 2 ^ 59
def prefixEnd_4971732 : Nat := 4983230072969 + 3 ^ 40 * 4971732 * 2
def baseEnd_4971732 : Nat := 2552888201339247309385427

theorem tailTrace_4971732 : CollatzResearch.WordTrace tailWord_4971732 prefixEnd_4971732 2552888201339247309385427 := by
  unfold tailWord_4971732
  simp only [CollatzResearch.WordTrace]
  refine ⟨90666981612135771535034725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120889308816181028713379633 90666981612135771535034725)
  ·
    refine ⟨17000059052275457162819011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90666981612135771535034725 17000059052275457162819011)
    ·
      refine ⟨25500088578413185744228517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17000059052275457162819011 25500088578413185744228517)
      ·
        refine ⟨4781266608452472327042847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25500088578413185744228517 4781266608452472327042847)
        ·
          refine ⟨7171899912678708490564271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4781266608452472327042847 7171899912678708490564271)
          ·
            refine ⟨10757849869018062735846407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7171899912678708490564271 10757849869018062735846407)
            ·
              refine ⟨16136774803527094103769611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10757849869018062735846407 16136774803527094103769611)
              ·
                refine ⟨24205162205290641155654417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16136774803527094103769611 24205162205290641155654417)
                ·
                  refine ⟨18153871653967980866740813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24205162205290641155654417 18153871653967980866740813)
                  ·
                    refine ⟨6807701870237992825027805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18153871653967980866740813 6807701870237992825027805)
                    ·
                      refine ⟨2552888201339247309385427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6807701870237992825027805 2552888201339247309385427)
                      ·
                        rfl

theorem cell23_4971732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_4971732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4971732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4971732 prefixEnd_4971732 := by exact prefixLift 4971732
  have htrace : WordTrace (prefixWord ++ tailWord_4971732) baseStart_4971732 baseEnd_4971732 := by
    simpa [prefixWord, tailWord_4971732, baseEnd_4971732] using wordTrace_append hprefix tailTrace_4971732
  have hstable : (prefixWord ++ tailWord_4971732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4971732).length < 2 ^ (prefixWord ++ tailWord_4971732).sum := by decide
  have hdescent : baseEnd_4971732 < baseStart_4971732 := by decide
  rcases family_descends (prefixWord ++ tailWord_4971732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4971748 : List Nat := [2, 3, 1, 1, 1, 2, 3, 1, 5, 4]
def baseStart_4971748 : Nat := 118140960795 + 4971748 * 2 ^ 59
def prefixEnd_4971748 : Nat := 4983230072969 + 3 ^ 40 * 4971748 * 2
def baseEnd_4971748 : Nat := 850965472343239748928451

theorem tailTrace_4971748 : CollatzResearch.WordTrace tailWord_4971748 prefixEnd_4971748 850965472343239748928451 := by
  unfold tailWord_4971748
  simp only [CollatzResearch.WordTrace]
  refine ⟨90667273396106788901325949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120889697861475718535101265 90667273396106788901325949)
  ·
    refine ⟨34000227523540045837997231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90667273396106788901325949 34000227523540045837997231)
    ·
      refine ⟨51000341285310068756995847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34000227523540045837997231 51000341285310068756995847)
      ·
        refine ⟨76500511927965103135493771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51000341285310068756995847 76500511927965103135493771)
        ·
          refine ⟨114750767891947654703240657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76500511927965103135493771 114750767891947654703240657)
          ·
            refine ⟨86063075918960741027430493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114750767891947654703240657 86063075918960741027430493)
            ·
              refine ⟨32273653469610277885286435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86063075918960741027430493 32273653469610277885286435)
              ·
                refine ⟨48410480204415416827929653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32273653469610277885286435 48410480204415416827929653)
                ·
                  refine ⟨4538482519163945327618405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48410480204415416827929653 4538482519163945327618405)
                  ·
                    refine ⟨850965472343239748928451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4538482519163945327618405 850965472343239748928451)
                    ·
                      rfl

theorem cell23_4971748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 5, 4].length) (baseStart_4971748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4971748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4971748 prefixEnd_4971748 := by exact prefixLift 4971748
  have htrace : WordTrace (prefixWord ++ tailWord_4971748) baseStart_4971748 baseEnd_4971748 := by
    simpa [prefixWord, tailWord_4971748, baseEnd_4971748] using wordTrace_append hprefix tailTrace_4971748
  have hstable : (prefixWord ++ tailWord_4971748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4971748).length < 2 ^ (prefixWord ++ tailWord_4971748).sum := by decide
  have hdescent : baseEnd_4971748 < baseStart_4971748 := by decide
  rcases family_descends (prefixWord ++ tailWord_4971748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4971755 : List Nat := [1, 1, 1, 1, 2, 8, 1, 1, 2, 1, 4]
def baseStart_4971755 : Nat := 118140960795 + 4971755 * 2 ^ 59
def prefixEnd_4971755 : Nat := 4983230072969 + 3 ^ 40 * 4971755 * 2
def baseEnd_4971755 : Nat := 2552900011394300719397821

theorem tailTrace_4971755 : CollatzResearch.WordTrace tailWord_4971755 prefixEnd_4971755 2552900011394300719397821 := by
  unfold tailWord_4971755
  simp only [CollatzResearch.WordTrace]
  refine ⟨181334802103188217998156719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120889868068792145332104479 181334802103188217998156719)
  ·
    refine ⟨272002203154782326997235079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181334802103188217998156719 272002203154782326997235079)
    ·
      refine ⟨408003304732173490495852619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272002203154782326997235079 408003304732173490495852619)
      ·
        refine ⟨612004957098260235743778929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 408003304732173490495852619 612004957098260235743778929)
        ·
          refine ⟨459003717823695176807834197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 612004957098260235743778929 459003717823695176807834197)
          ·
            refine ⟨5378949818246427853216807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 459003717823695176807834197 5378949818246427853216807)
            ·
              refine ⟨8068424727369641779825211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5378949818246427853216807 8068424727369641779825211)
              ·
                refine ⟨12102637091054462669737817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8068424727369641779825211 12102637091054462669737817)
                ·
                  refine ⟨9076977818290847002303363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12102637091054462669737817 9076977818290847002303363)
                  ·
                    refine ⟨13615466727436270503455045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9076977818290847002303363 13615466727436270503455045)
                    ·
                      refine ⟨2552900011394300719397821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13615466727436270503455045 2552900011394300719397821)
                      ·
                        rfl

theorem cell23_4971755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 1, 2, 1, 4].length) (baseStart_4971755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4971755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4971755 prefixEnd_4971755 := by exact prefixLift 4971755
  have htrace : WordTrace (prefixWord ++ tailWord_4971755) baseStart_4971755 baseEnd_4971755 := by
    simpa [prefixWord, tailWord_4971755, baseEnd_4971755] using wordTrace_append hprefix tailTrace_4971755
  have hstable : (prefixWord ++ tailWord_4971755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4971755).length < 2 ^ (prefixWord ++ tailWord_4971755).sum := by decide
  have hdescent : baseEnd_4971755 < baseStart_4971755 := by decide
  rcases family_descends (prefixWord ++ tailWord_4971755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4971761 : List Nat := [1, 2, 2, 2, 2, 1, 1, 4, 8]
def baseStart_4971761 : Nat := 118140960795 + 4971761 * 2 ^ 59
def prefixEnd_4971761 : Nat := 4983230072969 + 3 ^ 40 * 4971761 * 2
def baseEnd_4971761 : Nat := 283655899142025299546977

theorem tailTrace_4971761 : CollatzResearch.WordTrace tailWord_4971761 prefixEnd_4971761 283655899142025299546977 := by
  unfold tailWord_4971761
  simp only [CollatzResearch.WordTrace]
  refine ⟨181335020941166481022875137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120890013960777654015250091 181335020941166481022875137)
  ·
    refine ⟨136001265705874860767156353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181335020941166481022875137 136001265705874860767156353)
    ·
      refine ⟨102000949279406145575367265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136001265705874860767156353 102000949279406145575367265)
      ·
        refine ⟨76500711959554609181525449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102000949279406145575367265 76500711959554609181525449)
        ·
          refine ⟨57375533969665956886144087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76500711959554609181525449 57375533969665956886144087)
          ·
            refine ⟨86063300954498935329216131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57375533969665956886144087 86063300954498935329216131)
            ·
              refine ⟨129094951431748402993824197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86063300954498935329216131 129094951431748402993824197)
              ·
                refine ⟨24205303393452825561342037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 129094951431748402993824197 24205303393452825561342037)
                ·
                  refine ⟨283655899142025299546977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24205303393452825561342037 283655899142025299546977)
                  ·
                    rfl

theorem cell23_4971761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 8].length) (baseStart_4971761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4971761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4971761 prefixEnd_4971761 := by exact prefixLift 4971761
  have htrace : WordTrace (prefixWord ++ tailWord_4971761) baseStart_4971761 baseEnd_4971761 := by
    simpa [prefixWord, tailWord_4971761, baseEnd_4971761] using wordTrace_append hprefix tailTrace_4971761
  have hstable : (prefixWord ++ tailWord_4971761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4971761).length < 2 ^ (prefixWord ++ tailWord_4971761).sum := by decide
  have hdescent : baseEnd_4971761 < baseStart_4971761 := by decide
  rcases family_descends (prefixWord ++ tailWord_4971761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4971781 : List Nat := [1, 3, 1, 1, 2, 1, 3, 1, 1, 1, 8]
def baseStart_4971781 : Nat := 118140960795 + 4971781 * 2 ^ 59
def prefixEnd_4971781 : Nat := 4983230072969 + 3 ^ 40 * 4971781 * 2
def baseEnd_4971781 : Nat := 2552913361891317617672701

theorem tailTrace_4971781 : CollatzResearch.WordTrace tailWord_4971781 prefixEnd_4971781 2552913361891317617672701 := by
  unfold tailWord_4971781
  simp only [CollatzResearch.WordTrace]
  refine ⟨181335750401094024438603197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120890500267396016292402131 181335750401094024438603197)
  ·
    refine ⟨68000906400410259164476199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181335750401094024438603197 68000906400410259164476199)
    ·
      refine ⟨102001359600615388746714299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68000906400410259164476199 102001359600615388746714299)
      ·
        refine ⟨153002039400923083120071449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102001359600615388746714299 153002039400923083120071449)
        ·
          refine ⟨114751529550692312340053587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153002039400923083120071449 114751529550692312340053587)
          ·
            refine ⟨172127294326038468510080381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114751529550692312340053587 172127294326038468510080381)
            ·
              refine ⟨64547735372264425691280143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 172127294326038468510080381 64547735372264425691280143)
              ·
                refine ⟨96821603058396638536920215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64547735372264425691280143 96821603058396638536920215)
                ·
                  refine ⟨145232404587594957805380323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96821603058396638536920215 145232404587594957805380323)
                  ·
                    refine ⟨217848606881392436708070485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 145232404587594957805380323 217848606881392436708070485)
                    ·
                      refine ⟨2552913361891317617672701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 217848606881392436708070485 2552913361891317617672701)
                      ·
                        rfl

theorem cell23_4971781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 1, 8].length) (baseStart_4971781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4971781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4971781 prefixEnd_4971781 := by exact prefixLift 4971781
  have htrace : WordTrace (prefixWord ++ tailWord_4971781) baseStart_4971781 baseEnd_4971781 := by
    simpa [prefixWord, tailWord_4971781, baseEnd_4971781] using wordTrace_append hprefix tailTrace_4971781
  have hstable : (prefixWord ++ tailWord_4971781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4971781).length < 2 ^ (prefixWord ++ tailWord_4971781).sum := by decide
  have hdescent : baseEnd_4971781 < baseStart_4971781 := by decide
  rcases family_descends (prefixWord ++ tailWord_4971781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4971825 : List Nat := [1, 2, 2, 3, 3, 1, 2, 3, 1, 5]
def baseStart_4971825 : Nat := 118140960795 + 4971825 * 2 ^ 59
def prefixEnd_4971825 : Nat := 4983230072969 + 3 ^ 40 * 4971825 * 2
def baseEnd_4971825 : Nat := 850978651680038481840833

theorem tailTrace_4971825 : CollatzResearch.WordTrace tailWord_4971825 prefixEnd_4971825 850978651680038481840833 := by
  unfold tailWord_4971825
  simp only [CollatzResearch.WordTrace]
  refine ⟨181337355212934619953204929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120891570141956413302136619 181337355212934619953204929)
  ·
    refine ⟨136003016409700964964903697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181337355212934619953204929 136003016409700964964903697)
    ·
      refine ⟨102002262307275723723677773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136003016409700964964903697 102002262307275723723677773)
      ·
        refine ⟨38250848365228396396379165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102002262307275723723677773 38250848365228396396379165)
        ·
          refine ⟨14344068136960648648642187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38250848365228396396379165 14344068136960648648642187)
          ·
            refine ⟨21516102205440972972963281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14344068136960648648642187 21516102205440972972963281)
            ·
              refine ⟨16137076654080729729722461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21516102205440972972963281 16137076654080729729722461)
              ·
                refine ⟨6051403745280273648645923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16137076654080729729722461 6051403745280273648645923)
                ·
                  refine ⟨9077105617920410472968885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6051403745280273648645923 9077105617920410472968885)
                  ·
                    refine ⟨850978651680038481840833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9077105617920410472968885 850978651680038481840833)
                    ·
                      rfl

theorem cell23_4971825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 3, 1, 5].length) (baseStart_4971825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4971825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4971825 prefixEnd_4971825 := by exact prefixLift 4971825
  have htrace : WordTrace (prefixWord ++ tailWord_4971825) baseStart_4971825 baseEnd_4971825 := by
    simpa [prefixWord, tailWord_4971825, baseEnd_4971825] using wordTrace_append hprefix tailTrace_4971825
  have hstable : (prefixWord ++ tailWord_4971825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4971825).length < 2 ^ (prefixWord ++ tailWord_4971825).sum := by decide
  have hdescent : baseEnd_4971825 < baseStart_4971825 := by decide
  rcases family_descends (prefixWord ++ tailWord_4971825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4971848 : List Nat := [2, 1, 3, 1, 1, 2, 1, 1, 2, 6, 3]
def baseStart_4971848 : Nat := 118140960795 + 4971848 * 2 ^ 59
def prefixEnd_4971848 : Nat := 4983230072969 + 3 ^ 40 * 4971848 * 2
def baseEnd_4971848 : Nat := 2552947765095168855534893

theorem tailTrace_4971848 : CollatzResearch.WordTrace tailWord_4971848 prefixEnd_4971848 2552947765095168855534893 := by
  unfold tailWord_4971848
  simp only [CollatzResearch.WordTrace]
  refine ⟨90669097045925647440646099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120892129394567529920861465 90669097045925647440646099)
  ·
    refine ⟨136003645568888471160969149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90669097045925647440646099 136003645568888471160969149)
    ·
      refine ⟨51001367088333176685363431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136003645568888471160969149 51001367088333176685363431)
      ·
        refine ⟨76502050632499765028045147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51001367088333176685363431 76502050632499765028045147)
        ·
          refine ⟨114753075948749647542067721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76502050632499765028045147 114753075948749647542067721)
          ·
            refine ⟨86064806961562235656550791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114753075948749647542067721 86064806961562235656550791)
            ·
              refine ⟨129097210442343353484826187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86064806961562235656550791 129097210442343353484826187)
              ·
                refine ⟨193645815663515030227239281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129097210442343353484826187 193645815663515030227239281)
                ·
                  refine ⟨145234361747636272670429461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 193645815663515030227239281 145234361747636272670429461)
                  ·
                    refine ⟨6807860706920450281426381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 145234361747636272670429461 6807860706920450281426381)
                    ·
                      refine ⟨2552947765095168855534893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6807860706920450281426381 2552947765095168855534893)
                      ·
                        rfl

theorem cell23_4971848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 2, 6, 3].length) (baseStart_4971848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4971848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4971848 prefixEnd_4971848 := by exact prefixLift 4971848
  have htrace : WordTrace (prefixWord ++ tailWord_4971848) baseStart_4971848 baseEnd_4971848 := by
    simpa [prefixWord, tailWord_4971848, baseEnd_4971848] using wordTrace_append hprefix tailTrace_4971848
  have hstable : (prefixWord ++ tailWord_4971848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4971848).length < 2 ^ (prefixWord ++ tailWord_4971848).sum := by decide
  have hdescent : baseEnd_4971848 < baseStart_4971848 := by decide
  rcases family_descends (prefixWord ++ tailWord_4971848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4971875 : List Nat := [1, 1, 1, 5, 2, 3, 1, 2, 1, 2, 4]
def baseStart_4971875 : Nat := 118140960795 + 4971875 * 2 ^ 59
def prefixEnd_4971875 : Nat := 4983230072969 + 3 ^ 40 * 4971875 * 2
def baseEnd_4971875 : Nat := 2552961629072840249897269

theorem tailTrace_4971875 : CollatzResearch.WordTrace tailWord_4971875 prefixEnd_4971875 2552961629072840249897269 := by
  unfold tailWord_4971875
  simp only [CollatzResearch.WordTrace]
  refine ⟨181339178862753478492525079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120892785908502318995016719 181339178862753478492525079)
  ·
    refine ⟨272008768294130217738787619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181339178862753478492525079 272008768294130217738787619)
    ·
      refine ⟨408013152441195326608181429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272008768294130217738787619 408013152441195326608181429)
      ·
        refine ⟨38251233041362061869517009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 408013152441195326608181429 38251233041362061869517009)
        ·
          refine ⟨28688424781021546402137757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38251233041362061869517009 28688424781021546402137757)
          ·
            refine ⟨10758159292883079900801659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28688424781021546402137757 10758159292883079900801659)
            ·
              refine ⟨16137238939324619851202489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10758159292883079900801659 16137238939324619851202489)
              ·
                refine ⟨12102929204493464888401867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16137238939324619851202489 12102929204493464888401867)
                ·
                  refine ⟨18154393806740197332602801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12102929204493464888401867 18154393806740197332602801)
                  ·
                    refine ⟨13615795355055147999452101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18154393806740197332602801 13615795355055147999452101)
                    ·
                      refine ⟨2552961629072840249897269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13615795355055147999452101 2552961629072840249897269)
                      ·
                        rfl

theorem cell23_4971875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_4971875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4971875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4971875 prefixEnd_4971875 := by exact prefixLift 4971875
  have htrace : WordTrace (prefixWord ++ tailWord_4971875) baseStart_4971875 baseEnd_4971875 := by
    simpa [prefixWord, tailWord_4971875, baseEnd_4971875] using wordTrace_append hprefix tailTrace_4971875
  have hstable : (prefixWord ++ tailWord_4971875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4971875).length < 2 ^ (prefixWord ++ tailWord_4971875).sum := by decide
  have hdescent : baseEnd_4971875 < baseStart_4971875 := by decide
  rcases family_descends (prefixWord ++ tailWord_4971875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4971879 : List Nat := [1, 1, 5, 1, 4, 1, 3, 1, 1, 1, 4]
def baseStart_4971879 : Nat := 118140960795 + 4971879 * 2 ^ 59
def prefixEnd_4971879 : Nat := 4983230072969 + 3 ^ 40 * 4971879 * 2
def baseEnd_4971879 : Nat := 2552963682995458234247251

theorem tailTrace_4971879 : CollatzResearch.WordTrace tailWord_4971879 prefixEnd_4971879 2552963682995458234247251 := by
  unfold tailWord_4971879
  simp only [CollatzResearch.WordTrace]
  refine ⟨181339324754738987175670691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120892883169825991450447127 181339324754738987175670691)
  ·
    refine ⟨272008987132108480763506037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181339324754738987175670691 272008987132108480763506037)
    ·
      refine ⟨25500842543635170071578691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 272008987132108480763506037 25500842543635170071578691)
      ·
        refine ⟨38251263815452755107368037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25500842543635170071578691 38251263815452755107368037)
        ·
          refine ⟨7172111965397391582631507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38251263815452755107368037 7172111965397391582631507)
          ·
            refine ⟨10758167948096087373947261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7172111965397391582631507 10758167948096087373947261)
            ·
              refine ⟨4034312980536032765230223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10758167948096087373947261 4034312980536032765230223)
              ·
                refine ⟨6051469470804049147845335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4034312980536032765230223 6051469470804049147845335)
                ·
                  refine ⟨9077204206206073721768003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6051469470804049147845335 9077204206206073721768003)
                  ·
                    refine ⟨13615806309309110582652005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9077204206206073721768003 13615806309309110582652005)
                    ·
                      refine ⟨2552963682995458234247251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13615806309309110582652005 2552963682995458234247251)
                      ·
                        rfl

theorem cell23_4971879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 3, 1, 1, 1, 4].length) (baseStart_4971879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4971879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4971879 prefixEnd_4971879 := by exact prefixLift 4971879
  have htrace : WordTrace (prefixWord ++ tailWord_4971879) baseStart_4971879 baseEnd_4971879 := by
    simpa [prefixWord, tailWord_4971879, baseEnd_4971879] using wordTrace_append hprefix tailTrace_4971879
  have hstable : (prefixWord ++ tailWord_4971879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4971879).length < 2 ^ (prefixWord ++ tailWord_4971879).sum := by decide
  have hdescent : baseEnd_4971879 < baseStart_4971879 := by decide
  rcases family_descends (prefixWord ++ tailWord_4971879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4971912 : List Nat := [2, 1, 3, 3, 1, 3, 2, 1, 1, 3, 3]
def baseStart_4971912 : Nat := 118140960795 + 4971912 * 2 ^ 59
def prefixEnd_4971912 : Nat := 4983230072969 + 3 ^ 40 * 4971912 * 2
def baseEnd_4971912 : Nat := 2552980627857056605134599

theorem tailTrace_4971912 : CollatzResearch.WordTrace tailWord_4971912 prefixEnd_4971912 2552980627857056605134599 := by
  unfold tailWord_4971912
  simp only [CollatzResearch.WordTrace]
  refine ⟨90670264181809716905810995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120893685575746289207747993 90670264181809716905810995)
  ·
    refine ⟨136005396272714575358716493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90670264181809716905810995 136005396272714575358716493)
    ·
      refine ⟨51002023602267965759518685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136005396272714575358716493 51002023602267965759518685)
      ·
        refine ⟨19125758850850487159819507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51002023602267965759518685 19125758850850487159819507)
        ·
          refine ⟨28688638276275730739729261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19125758850850487159819507 28688638276275730739729261)
          ·
            refine ⟨10758239353603399027398473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28688638276275730739729261 10758239353603399027398473)
            ·
              refine ⟨8068679515202549270548855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10758239353603399027398473 8068679515202549270548855)
              ·
                refine ⟨12103019272803823905823283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8068679515202549270548855 12103019272803823905823283)
                ·
                  refine ⟨18154528909205735858734925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12103019272803823905823283 18154528909205735858734925)
                  ·
                    refine ⟨6807948340952150947025597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18154528909205735858734925 6807948340952150947025597)
                    ·
                      refine ⟨2552980627857056605134599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6807948340952150947025597 2552980627857056605134599)
                      ·
                        rfl

theorem cell23_4971912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_4971912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4971912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4971912 prefixEnd_4971912 := by exact prefixLift 4971912
  have htrace : WordTrace (prefixWord ++ tailWord_4971912) baseStart_4971912 baseEnd_4971912 := by
    simpa [prefixWord, tailWord_4971912, baseEnd_4971912] using wordTrace_append hprefix tailTrace_4971912
  have hstable : (prefixWord ++ tailWord_4971912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4971912).length < 2 ^ (prefixWord ++ tailWord_4971912).sum := by decide
  have hdescent : baseEnd_4971912 < baseStart_4971912 := by decide
  rcases family_descends (prefixWord ++ tailWord_4971912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4971965 : List Nat := [1, 4, 1, 2, 2, 1, 1, 3, 2, 2, 4]
def baseStart_4971965 : Nat := 118140960795 + 4971965 * 2 ^ 59
def prefixEnd_4971965 : Nat := 4983230072969 + 3 ^ 40 * 4971965 * 2
def baseEnd_4971965 : Nat := 2553007842331744897771855

theorem tailTrace_4971965 : CollatzResearch.WordTrace tailWord_4971965 prefixEnd_4971965 2553007842331744897771855 := by
  unfold tailWord_4971965
  simp only [CollatzResearch.WordTrace]
  refine ⟨181342461432427423863301349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120894974288284949242200899 181342461432427423863301349)
  ·
    refine ⟨34001711518580141974369003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 181342461432427423863301349 34001711518580141974369003)
    ·
      refine ⟨51002567277870212961553505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34001711518580141974369003 51002567277870212961553505)
      ·
        refine ⟨38251925458402659721165129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51002567277870212961553505 38251925458402659721165129)
        ·
          refine ⟨28688944093801994790873847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38251925458402659721165129 28688944093801994790873847)
          ·
            refine ⟨43033416140702992186310771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28688944093801994790873847 43033416140702992186310771)
            ·
              refine ⟨64550124211054488279466157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43033416140702992186310771 64550124211054488279466157)
              ·
                refine ⟨24206296579145433104799809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64550124211054488279466157 24206296579145433104799809)
                ·
                  refine ⟨18154722434359074828599857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24206296579145433104799809 18154722434359074828599857)
                  ·
                    refine ⟨13616041825769306121449893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18154722434359074828599857 13616041825769306121449893)
                    ·
                      refine ⟨2553007842331744897771855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13616041825769306121449893 2553007842331744897771855)
                      ·
                        rfl

theorem cell23_4971965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_4971965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4971965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4971965 prefixEnd_4971965 := by exact prefixLift 4971965
  have htrace : WordTrace (prefixWord ++ tailWord_4971965) baseStart_4971965 baseEnd_4971965 := by
    simpa [prefixWord, tailWord_4971965, baseEnd_4971965] using wordTrace_append hprefix tailTrace_4971965
  have hstable : (prefixWord ++ tailWord_4971965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4971965).length < 2 ^ (prefixWord ++ tailWord_4971965).sum := by decide
  have hdescent : baseEnd_4971965 < baseStart_4971965 := by decide
  rcases family_descends (prefixWord ++ tailWord_4971965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4971970 : List Nat := [3, 5, 2, 1, 2, 1, 2, 7]
def baseStart_4971970 : Nat := 118140960795 + 4971970 * 2 ^ 59
def prefixEnd_4971970 : Nat := 4983230072969 + 3 ^ 40 * 4971970 * 2
def baseEnd_4971970 : Nat := 94555941101296939933679

theorem tailTrace_4971970 : CollatzResearch.WordTrace tailWord_4971970 prefixEnd_4971970 94555941101296939933679 := by
  unfold tailWord_4971970
  simp only [CollatzResearch.WordTrace]
  refine ⟨45335660949352327429308341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120895095864939539811488909 45335660949352327429308341)
  ·
    refine ⟨4250218214001780696497657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45335660949352327429308341 4250218214001780696497657)
    ·
      refine ⟨3187663660501335522373243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4250218214001780696497657 3187663660501335522373243)
      ·
        refine ⟨4781495490752003283559865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3187663660501335522373243 4781495490752003283559865)
        ·
          refine ⟨3586121618064002462669899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4781495490752003283559865 3586121618064002462669899)
          ·
            refine ⟨5379182427096003694004849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3586121618064002462669899 5379182427096003694004849)
            ·
              refine ⟨4034386820322002770503637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5379182427096003694004849 4034386820322002770503637)
              ·
                refine ⟨94555941101296939933679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4034386820322002770503637 94555941101296939933679)
                ·
                  rfl

theorem cell23_4971970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 2, 7].length) (baseStart_4971970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4971970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4971970 prefixEnd_4971970 := by exact prefixLift 4971970
  have htrace : WordTrace (prefixWord ++ tailWord_4971970) baseStart_4971970 baseEnd_4971970 := by
    simpa [prefixWord, tailWord_4971970, baseEnd_4971970] using wordTrace_append hprefix tailTrace_4971970
  have hstable : (prefixWord ++ tailWord_4971970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4971970).length < 2 ^ (prefixWord ++ tailWord_4971970).sum := by decide
  have hdescent : baseEnd_4971970 < baseStart_4971970 := by decide
  rcases family_descends (prefixWord ++ tailWord_4971970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4971992 : List Nat := [2, 1, 2, 2, 2, 1, 5, 3, 5]
def baseStart_4971992 : Nat := 118140960795 + 4971992 * 2 ^ 59
def prefixEnd_4971992 : Nat := 4983230072969 + 3 ^ 40 * 4971992 * 2
def baseEnd_4971992 : Nat := 283669078478824032459359

theorem tailTrace_4971992 : CollatzResearch.WordTrace tailWord_4971992 prefixEnd_4971992 283669078478824032459359 := by
  unfold tailWord_4971992
  simp only [CollatzResearch.WordTrace]
  refine ⟨90671723101664803737267115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120895630802219738316356153 90671723101664803737267115)
  ·
    refine ⟨136007584652497205605900673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90671723101664803737267115 136007584652497205605900673)
    ·
      refine ⟨102005688489372904204425505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136007584652497205605900673 102005688489372904204425505)
      ·
        refine ⟨76504266367029678153319129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102005688489372904204425505 76504266367029678153319129)
        ·
          refine ⟨57378199775272258614989347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76504266367029678153319129 57378199775272258614989347)
          ·
            refine ⟨86067299662908387922484021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57378199775272258614989347 86067299662908387922484021)
            ·
              refine ⟨8068809343397661367732877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 86067299662908387922484021 8068809343397661367732877)
              ·
                refine ⟨3025803503774123012899829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8068809343397661367732877 3025803503774123012899829)
                ·
                  refine ⟨283669078478824032459359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3025803503774123012899829 283669078478824032459359)
                  ·
                    rfl

theorem cell23_4971992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 3, 5].length) (baseStart_4971992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4971992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4971992 prefixEnd_4971992 := by exact prefixLift 4971992
  have htrace : WordTrace (prefixWord ++ tailWord_4971992) baseStart_4971992 baseEnd_4971992 := by
    simpa [prefixWord, tailWord_4971992, baseEnd_4971992] using wordTrace_append hprefix tailTrace_4971992
  have hstable : (prefixWord ++ tailWord_4971992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4971992).length < 2 ^ (prefixWord ++ tailWord_4971992).sum := by decide
  have hdescent : baseEnd_4971992 < baseStart_4971992 := by decide
  rcases family_descends (prefixWord ++ tailWord_4971992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4972025 : List Nat := [1, 2, 1, 3, 1, 2, 1, 1, 6, 1, 4]
def baseStart_4972025 : Nat := 118140960795 + 4972025 * 2 ^ 59
def prefixEnd_4972025 : Nat := 4983230072969 + 3 ^ 40 * 4972025 * 2
def baseEnd_4972025 : Nat := 2553038651171014663021579

theorem tailTrace_4972025 : CollatzResearch.WordTrace tailWord_4972025 prefixEnd_4972025 2553038651171014663021579 := by
  unfold tailWord_4972025
  simp only [CollatzResearch.WordTrace]
  refine ⟨181344649812210054110485529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120896433208140036073657019 181344649812210054110485529)
  ·
    refine ⟨136008487359157540582864147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181344649812210054110485529 136008487359157540582864147)
    ·
      refine ⟨204012731038736310874296221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136008487359157540582864147 204012731038736310874296221)
      ·
        refine ⟨76504774139526116577861083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 204012731038736310874296221 76504774139526116577861083)
        ·
          refine ⟨114757161209289174866791625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76504774139526116577861083 114757161209289174866791625)
          ·
            refine ⟨86067870906966881150093719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114757161209289174866791625 86067870906966881150093719)
            ·
              refine ⟨129101806360450321725140579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86067870906966881150093719 129101806360450321725140579)
              ·
                refine ⟨193652709540675482587710869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129101806360450321725140579 193652709540675482587710869)
                ·
                  refine ⟨9077470759719163246298947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 193652709540675482587710869 9077470759719163246298947)
                  ·
                    refine ⟨13616206139578744869448421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9077470759719163246298947 13616206139578744869448421)
                    ·
                      refine ⟨2553038651171014663021579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13616206139578744869448421 2553038651171014663021579)
                      ·
                        rfl

theorem cell23_4972025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 6, 1, 4].length) (baseStart_4972025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4972025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4972025 prefixEnd_4972025 := by exact prefixLift 4972025
  have htrace : WordTrace (prefixWord ++ tailWord_4972025) baseStart_4972025 baseEnd_4972025 := by
    simpa [prefixWord, tailWord_4972025, baseEnd_4972025] using wordTrace_append hprefix tailTrace_4972025
  have hstable : (prefixWord ++ tailWord_4972025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4972025).length < 2 ^ (prefixWord ++ tailWord_4972025).sum := by decide
  have hdescent : baseEnd_4972025 < baseStart_4972025 := by decide
  rcases family_descends (prefixWord ++ tailWord_4972025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4972042 : List Nat := [3, 1, 2, 2, 2, 2, 1, 3, 2, 1, 4]
def baseStart_4972042 : Nat := 118140960795 + 4972042 * 2 ^ 59
def prefixEnd_4972042 : Nat := 4983230072969 + 3 ^ 40 * 4972042 * 2
def baseEnd_4972042 : Nat := 2553047380342141096509001

theorem tailTrace_4972042 : CollatzResearch.WordTrace tailWord_4972042 prefixEnd_4972042 2553047380342141096509001 := by
  unfold tailWord_4972042
  simp only [CollatzResearch.WordTrace]
  refine ⟨45336317463287116503463595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120896846568765644009236253 45336317463287116503463595)
  ·
    refine ⟨68004476194930674755195393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45336317463287116503463595 68004476194930674755195393)
    ·
      refine ⟨51003357146198006066396545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68004476194930674755195393 51003357146198006066396545)
      ·
        refine ⟨38252517859648504549797409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51003357146198006066396545 38252517859648504549797409)
        ·
          refine ⟨28689388394736378412348057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38252517859648504549797409 28689388394736378412348057)
          ·
            refine ⟨21517041296052283809261043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28689388394736378412348057 21517041296052283809261043)
            ·
              refine ⟨32275561944078425713891565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21517041296052283809261043 32275561944078425713891565)
              ·
                refine ⟨12103335729029409642709337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32275561944078425713891565 12103335729029409642709337)
                ·
                  refine ⟨9077501796772057232032003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12103335729029409642709337 9077501796772057232032003)
                  ·
                    refine ⟨13616252695158085848048005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9077501796772057232032003 13616252695158085848048005)
                    ·
                      refine ⟨2553047380342141096509001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13616252695158085848048005 2553047380342141096509001)
                      ·
                        rfl

theorem cell23_4972042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_4972042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4972042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4972042 prefixEnd_4972042 := by exact prefixLift 4972042
  have htrace : WordTrace (prefixWord ++ tailWord_4972042) baseStart_4972042 baseEnd_4972042 := by
    simpa [prefixWord, tailWord_4972042, baseEnd_4972042] using wordTrace_append hprefix tailTrace_4972042
  have hstable : (prefixWord ++ tailWord_4972042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4972042).length < 2 ^ (prefixWord ++ tailWord_4972042).sum := by decide
  have hdescent : baseEnd_4972042 < baseStart_4972042 := by decide
  rcases family_descends (prefixWord ++ tailWord_4972042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4972075 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 4, 5, 3]
def baseStart_4972075 : Nat := 118140960795 + 4972075 * 2 ^ 59
def prefixEnd_4972075 : Nat := 4983230072969 + 3 ^ 40 * 4972075 * 2
def baseEnd_4972075 : Nat := 2553064325203739467396349

theorem tailTrace_4972075 : CollatzResearch.WordTrace tailWord_4972075 prefixEnd_4972075 2553064325203739467396349 := by
  unfold tailWord_4972075
  simp only [CollatzResearch.WordTrace]
  refine ⟨181346473462028912649805679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120897648974685941766537119 181346473462028912649805679)
  ·
    refine ⟨272019710193043368974708519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181346473462028912649805679 272019710193043368974708519)
    ·
      refine ⟨408029565289565053462062779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272019710193043368974708519 408029565289565053462062779)
      ·
        refine ⟨612044347934347580193094169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 408029565289565053462062779 612044347934347580193094169)
        ·
          refine ⟨459033260950760685144820627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 612044347934347580193094169 459033260950760685144820627)
          ·
            refine ⟨688549891426141027717230941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 459033260950760685144820627 688549891426141027717230941)
            ·
              refine ⟨258206209284802885393961603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 688549891426141027717230941 258206209284802885393961603)
              ·
                refine ⟨387309313927204328090942405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 258206209284802885393961603 387309313927204328090942405)
                ·
                  refine ⟨72620496361350811517051701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 387309313927204328090942405 72620496361350811517051701)
                  ·
                    refine ⟨6808171533876638579723597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 72620496361350811517051701 6808171533876638579723597)
                    ·
                      refine ⟨2553064325203739467396349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6808171533876638579723597 2553064325203739467396349)
                      ·
                        rfl

theorem cell23_4972075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 5, 3].length) (baseStart_4972075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4972075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4972075 prefixEnd_4972075 := by exact prefixLift 4972075
  have htrace : WordTrace (prefixWord ++ tailWord_4972075) baseStart_4972075 baseEnd_4972075 := by
    simpa [prefixWord, tailWord_4972075, baseEnd_4972075] using wordTrace_append hprefix tailTrace_4972075
  have hstable : (prefixWord ++ tailWord_4972075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4972075).length < 2 ^ (prefixWord ++ tailWord_4972075).sum := by decide
  have hdescent : baseEnd_4972075 < baseStart_4972075 := by decide
  rcases family_descends (prefixWord ++ tailWord_4972075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4972086 : List Nat := [5, 1, 2, 1, 3, 1, 1, 2, 3, 4]
def baseStart_4972086 : Nat := 118140960795 + 4972086 * 2 ^ 59
def prefixEnd_4972086 : Nat := 4983230072969 + 3 ^ 40 * 4972086 * 2
def baseEnd_4972086 : Nat := 851023324496979641452933

theorem tailTrace_4972086 : CollatzResearch.WordTrace tailWord_4972086 prefixEnd_4972086 851023324496979641452933 := by
  unfold tailWord_4972086
  simp only [CollatzResearch.WordTrace]
  refine ⟨11334179666561816345528507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 120897916443326041018970741 11334179666561816345528507)
  ·
    refine ⟨17001269499842724518292761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11334179666561816345528507 17001269499842724518292761)
    ·
      refine ⟨12750952124882043388719571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17001269499842724518292761 12750952124882043388719571)
      ·
        refine ⟨19126428187323065083079357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12750952124882043388719571 19126428187323065083079357)
        ·
          refine ⟨7172410570246149406154759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19126428187323065083079357 7172410570246149406154759)
          ·
            refine ⟨10758615855369224109232139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7172410570246149406154759 10758615855369224109232139)
            ·
              refine ⟨16137923783053836163848209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10758615855369224109232139 16137923783053836163848209)
              ·
                refine ⟨12103442837290377122886157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16137923783053836163848209 12103442837290377122886157)
                ·
                  refine ⟨4538791063983891421082309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12103442837290377122886157 4538791063983891421082309)
                  ·
                    refine ⟨851023324496979641452933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4538791063983891421082309 851023324496979641452933)
                    ·
                      rfl

theorem cell23_4972086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_4972086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4972086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4972086 prefixEnd_4972086 := by exact prefixLift 4972086
  have htrace : WordTrace (prefixWord ++ tailWord_4972086) baseStart_4972086 baseEnd_4972086 := by
    simpa [prefixWord, tailWord_4972086, baseEnd_4972086] using wordTrace_append hprefix tailTrace_4972086
  have hstable : (prefixWord ++ tailWord_4972086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4972086).length < 2 ^ (prefixWord ++ tailWord_4972086).sum := by decide
  have hdescent : baseEnd_4972086 < baseStart_4972086 := by decide
  rcases family_descends (prefixWord ++ tailWord_4972086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4972112 : List Nat := [2, 1, 1, 1, 1, 3, 5, 3, 1, 5]
def baseStart_4972112 : Nat := 118140960795 + 4972112 * 2 ^ 59
def prefixEnd_4972112 : Nat := 4983230072969 + 3 ^ 40 * 4972112 * 2
def baseEnd_4972112 : Nat := 851027774662651940877893

theorem tailTrace_4972112 : CollatzResearch.WordTrace tailWord_4972112 prefixEnd_4972112 851027774662651940877893 := by
  unfold tailWord_4972112
  simp only [CollatzResearch.WordTrace]
  refine ⟨90673911481447433984451295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120898548641929911979268393 90673911481447433984451295)
  ·
    refine ⟨136010867222171150976676943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90673911481447433984451295 136010867222171150976676943)
    ·
      refine ⟨204016300833256726465015415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136010867222171150976676943 204016300833256726465015415)
      ·
        refine ⟨306024451249885089697523123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204016300833256726465015415 306024451249885089697523123)
        ·
          refine ⟨459036676874827634546284685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 306024451249885089697523123 459036676874827634546284685)
          ·
            refine ⟨172138753828060362954856757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 459036676874827634546284685 172138753828060362954856757)
            ·
              refine ⟨16138008171380659027017821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 172138753828060362954856757 16138008171380659027017821)
              ·
                refine ⟨6051753064267747135131683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16138008171380659027017821 6051753064267747135131683)
                ·
                  refine ⟨9077629596401620702697525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6051753064267747135131683 9077629596401620702697525)
                  ·
                    refine ⟨851027774662651940877893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9077629596401620702697525 851027774662651940877893)
                    ·
                      rfl

theorem cell23_4972112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 3, 1, 5].length) (baseStart_4972112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4972112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4972112 prefixEnd_4972112 := by exact prefixLift 4972112
  have htrace : WordTrace (prefixWord ++ tailWord_4972112) baseStart_4972112 baseEnd_4972112 := by
    simpa [prefixWord, tailWord_4972112, baseEnd_4972112] using wordTrace_append hprefix tailTrace_4972112
  have hstable : (prefixWord ++ tailWord_4972112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4972112).length < 2 ^ (prefixWord ++ tailWord_4972112).sum := by decide
  have hdescent : baseEnd_4972112 < baseStart_4972112 := by decide
  rcases family_descends (prefixWord ++ tailWord_4972112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4972155 : List Nat := [1, 1, 1, 1, 1, 4, 5, 9]
def baseStart_4972155 : Nat := 118140960795 + 4972155 * 2 ^ 59
def prefixEnd_4972155 : Nat := 4983230072969 + 3 ^ 40 * 4972155 * 2
def baseEnd_4972155 : Nat := 94559459394670339051703

theorem tailTrace_4972155 : CollatzResearch.WordTrace tailWord_4972155 prefixEnd_4972155 94559459394670339051703 := by
  unfold tailWord_4972155
  simp only [CollatzResearch.WordTrace]
  refine ⟨181349391301739086312717919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120899594201159390875145279 181349391301739086312717919)
  ·
    refine ⟨272024086952608629469076879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181349391301739086312717919 272024086952608629469076879)
    ·
      refine ⟨408036130428912944203615319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272024086952608629469076879 408036130428912944203615319)
      ·
        refine ⟨612054195643369416305422979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 408036130428912944203615319 612054195643369416305422979)
        ·
          refine ⟨918081293465054124458134469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 612054195643369416305422979 918081293465054124458134469)
          ·
            refine ⟨172140242524697648335900213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 918081293465054124458134469 172140242524697648335900213)
            ·
              refine ⟨16138147736690404531490645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 172140242524697648335900213 16138147736690404531490645)
              ·
                refine ⟨94559459394670339051703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16138147736690404531490645 94559459394670339051703)
                ·
                  rfl

theorem cell23_4972155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 9].length) (baseStart_4972155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4972155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4972155 prefixEnd_4972155 := by exact prefixLift 4972155
  have htrace : WordTrace (prefixWord ++ tailWord_4972155) baseStart_4972155 baseEnd_4972155 := by
    simpa [prefixWord, tailWord_4972155, baseEnd_4972155] using wordTrace_append hprefix tailTrace_4972155
  have hstable : (prefixWord ++ tailWord_4972155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4972155).length < 2 ^ (prefixWord ++ tailWord_4972155).sum := by decide
  have hdescent : baseEnd_4972155 < baseStart_4972155 := by decide
  rcases family_descends (prefixWord ++ tailWord_4972155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4972169 : List Nat := [1, 2, 1, 1, 4, 1, 4, 3, 1, 2, 3]
def baseStart_4972169 : Nat := 118140960795 + 4972169 * 2 ^ 59
def prefixEnd_4972169 : Nat := 4983230072969 + 3 ^ 40 * 4972169 * 2
def baseEnd_4972169 : Nat := 2553112592385262099620917

theorem tailTrace_4972169 : CollatzResearch.WordTrace tailWord_4972169 prefixEnd_4972169 2553112592385262099620917 := by
  unfold tailWord_4972169
  simp only [CollatzResearch.WordTrace]
  refine ⟨181349901923688366703727561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120899934615792244469151707 181349901923688366703727561)
  ·
    refine ⟨136012426442766275027795671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181349901923688366703727561 136012426442766275027795671)
    ·
      refine ⟨204018639664149412541693507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136012426442766275027795671 204018639664149412541693507)
      ·
        refine ⟨306027959496224118812540261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204018639664149412541693507 306027959496224118812540261)
        ·
          refine ⟨57380242405542022277351299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 306027959496224118812540261 57380242405542022277351299)
          ·
            refine ⟨86070363608313033416026949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57380242405542022277351299 86070363608313033416026949)
            ·
              refine ⟨16138193176558693765505053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86070363608313033416026949 16138193176558693765505053)
              ·
                refine ⟨6051822441209510162064395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16138193176558693765505053 6051822441209510162064395)
                ·
                  refine ⟨9077733661814265243096593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6051822441209510162064395 9077733661814265243096593)
                  ·
                    refine ⟨6808300246360698932322445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9077733661814265243096593 6808300246360698932322445)
                    ·
                      refine ⟨2553112592385262099620917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6808300246360698932322445 2553112592385262099620917)
                      ·
                        rfl

theorem cell23_4972169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 3, 1, 2, 3].length) (baseStart_4972169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4972169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4972169 prefixEnd_4972169 := by exact prefixLift 4972169
  have htrace : WordTrace (prefixWord ++ tailWord_4972169) baseStart_4972169 baseEnd_4972169 := by
    simpa [prefixWord, tailWord_4972169, baseEnd_4972169] using wordTrace_append hprefix tailTrace_4972169
  have hstable : (prefixWord ++ tailWord_4972169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4972169).length < 2 ^ (prefixWord ++ tailWord_4972169).sum := by decide
  have hdescent : baseEnd_4972169 < baseStart_4972169 := by decide
  rcases family_descends (prefixWord ++ tailWord_4972169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4972175 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 6]
def baseStart_4972175 : Nat := 118140960795 + 4972175 * 2 ^ 59
def prefixEnd_4972175 : Nat := 4983230072969 + 3 ^ 40 * 4972175 * 2
def baseEnd_4972175 : Nat := 2553115673269189076145889

theorem tailTrace_4972175 : CollatzResearch.WordTrace tailWord_4972175 prefixEnd_4972175 2553115673269189076145889 := by
  unfold tailWord_4972175
  simp only [CollatzResearch.WordTrace]
  refine ⟨181350120761666629728445979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120900080507777753152297319 181350120761666629728445979)
  ·
    refine ⟨272025181142499944592668969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181350120761666629728445979 272025181142499944592668969)
    ·
      refine ⟨204018885856874958444501727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 272025181142499944592668969 204018885856874958444501727)
      ·
        refine ⟨306028328785312437666752591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204018885856874958444501727 306028328785312437666752591)
        ·
          refine ⟨459042493177968656500128887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 306028328785312437666752591 459042493177968656500128887)
          ·
            refine ⟨688563739766952984750193331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 459042493177968656500128887 688563739766952984750193331)
            ·
              refine ⟨1032845609650429477125289997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 688563739766952984750193331 1032845609650429477125289997)
              ·
                refine ⟨387317103618911053921983749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1032845609650429477125289997 387317103618911053921983749)
                ·
                  refine ⟨72621956928545822610371953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 387317103618911053921983749 72621956928545822610371953)
                  ·
                    refine ⟨54466467696409366957778965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 72621956928545822610371953 54466467696409366957778965)
                    ·
                      refine ⟨2553115673269189076145889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54466467696409366957778965 2553115673269189076145889)
                      ·
                        rfl

theorem cell23_4972175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 6].length) (baseStart_4972175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4972175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4972175 prefixEnd_4972175 := by exact prefixLift 4972175
  have htrace : WordTrace (prefixWord ++ tailWord_4972175) baseStart_4972175 baseEnd_4972175 := by
    simpa [prefixWord, tailWord_4972175, baseEnd_4972175] using wordTrace_append hprefix tailTrace_4972175
  have hstable : (prefixWord ++ tailWord_4972175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4972175).length < 2 ^ (prefixWord ++ tailWord_4972175).sum := by decide
  have hdescent : baseEnd_4972175 < baseStart_4972175 := by decide
  rcases family_descends (prefixWord ++ tailWord_4972175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4972183 : List Nat := [1, 1, 3, 3, 2, 4, 1, 1, 3, 2, 2]
def baseStart_4972183 : Nat := 118140960795 + 4972183 * 2 ^ 59
def prefixEnd_4972183 : Nat := 4983230072969 + 3 ^ 40 * 4972183 * 2
def baseEnd_4972183 : Nat := 2553119781114425044845853

theorem tailTrace_4972183 : CollatzResearch.WordTrace tailWord_4972183 prefixEnd_4972183 2553119781114425044845853 := by
  unfold tailWord_4972183
  simp only [CollatzResearch.WordTrace]
  refine ⟨181350412545637647094737203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120900275030425098063158135 181350412545637647094737203)
  ·
    refine ⟨272025618818456470642105805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181350412545637647094737203 272025618818456470642105805)
    ·
      refine ⟨102009607056921176490789677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 272025618818456470642105805 102009607056921176490789677)
      ·
        refine ⟨38253602646345441184046129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102009607056921176490789677 38253602646345441184046129)
        ·
          refine ⟨28690201984759080888034597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38253602646345441184046129 28690201984759080888034597)
          ·
            refine ⟨5379412872142327666506487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28690201984759080888034597 5379412872142327666506487)
            ·
              refine ⟨8069119308213491499759731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5379412872142327666506487 8069119308213491499759731)
              ·
                refine ⟨12103678962320237249639597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8069119308213491499759731 12103678962320237249639597)
                ·
                  refine ⟨4538879610870088968614849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12103678962320237249639597 4538879610870088968614849)
                  ·
                    refine ⟨3404159708152566726461137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4538879610870088968614849 3404159708152566726461137)
                    ·
                      refine ⟨2553119781114425044845853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3404159708152566726461137 2553119781114425044845853)
                      ·
                        rfl

theorem cell23_4972183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 1, 3, 2, 2].length) (baseStart_4972183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4972183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4972183 prefixEnd_4972183 := by exact prefixLift 4972183
  have htrace : WordTrace (prefixWord ++ tailWord_4972183) baseStart_4972183 baseEnd_4972183 := by
    simpa [prefixWord, tailWord_4972183, baseEnd_4972183] using wordTrace_append hprefix tailTrace_4972183
  have hstable : (prefixWord ++ tailWord_4972183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4972183).length < 2 ^ (prefixWord ++ tailWord_4972183).sum := by decide
  have hdescent : baseEnd_4972183 < baseStart_4972183 := by decide
  rcases family_descends (prefixWord ++ tailWord_4972183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4972193 : List Nat := [1, 2, 3, 3, 2, 3, 2, 1, 2, 4]
def baseStart_4972193 : Nat := 118140960795 + 4972193 * 2 ^ 59
def prefixEnd_4972193 : Nat := 4983230072969 + 3 ^ 40 * 4972193 * 2
def baseEnd_4972193 : Nat := 851041638640323335240269

theorem tailTrace_4972193 : CollatzResearch.WordTrace tailWord_4972193 prefixEnd_4972193 851041638640323335240269 := by
  unfold tailWord_4972193
  simp only [CollatzResearch.WordTrace]
  refine ⟨181350777275601418802601233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120900518183734279201734155 181350777275601418802601233)
  ·
    refine ⟨136013082956701064101950925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181350777275601418802601233 136013082956701064101950925)
    ·
      refine ⟨51004906108762899038231597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136013082956701064101950925 51004906108762899038231597)
      ·
        refine ⟨19126839790786087139336849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51004906108762899038231597 19126839790786087139336849)
        ·
          refine ⟨14345129843089565354502637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19126839790786087139336849 14345129843089565354502637)
          ·
            refine ⟨5379423691158587007938489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14345129843089565354502637 5379423691158587007938489)
            ·
              refine ⟨4034567768368940255953867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5379423691158587007938489 4034567768368940255953867)
              ·
                refine ⟨6051851652553410383930801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4034567768368940255953867 6051851652553410383930801)
                ·
                  refine ⟨4538888739415057787948101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6051851652553410383930801 4538888739415057787948101)
                  ·
                    refine ⟨851041638640323335240269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4538888739415057787948101 851041638640323335240269)
                    ·
                      rfl

theorem cell23_4972193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 2, 1, 2, 4].length) (baseStart_4972193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4972193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4972193 prefixEnd_4972193 := by exact prefixLift 4972193
  have htrace : WordTrace (prefixWord ++ tailWord_4972193) baseStart_4972193 baseEnd_4972193 := by
    simpa [prefixWord, tailWord_4972193, baseEnd_4972193] using wordTrace_append hprefix tailTrace_4972193
  have hstable : (prefixWord ++ tailWord_4972193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4972193).length < 2 ^ (prefixWord ++ tailWord_4972193).sum := by decide
  have hdescent : baseEnd_4972193 < baseStart_4972193 := by decide
  rcases family_descends (prefixWord ++ tailWord_4972193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4972232 : List Nat := [2, 1, 3, 1, 2, 2, 2, 2, 2, 6]
def baseStart_4972232 : Nat := 118140960795 + 4972232 * 2 ^ 59
def prefixEnd_4972232 : Nat := 4983230072969 + 3 ^ 40 * 4972232 * 2
def baseEnd_4972232 : Nat := 851048313888831784377709

theorem tailTrace_4972232 : CollatzResearch.WordTrace tailWord_4972232 prefixEnd_4972232 851048313888831784377709 := by
  unfold tailWord_4972232
  simp only [CollatzResearch.WordTrace]
  refine ⟨90676099861230064231635475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120901466481640085642180633 90676099861230064231635475)
  ·
    refine ⟨136014149791845096347453213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90676099861230064231635475 136014149791845096347453213)
    ·
      refine ⟨51005306171941911130294955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136014149791845096347453213 51005306171941911130294955)
      ·
        refine ⟨76507959257912866695442433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51005306171941911130294955 76507959257912866695442433)
        ·
          refine ⟨57380969443434650021581825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76507959257912866695442433 57380969443434650021581825)
          ·
            refine ⟨43035727082575987516186369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57380969443434650021581825 43035727082575987516186369)
            ·
              refine ⟨32276795311931990637139777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43035727082575987516186369 32276795311931990637139777)
              ·
                refine ⟨24207596483948992977854833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32276795311931990637139777 24207596483948992977854833)
                ·
                  refine ⟨18155697362961744733391125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24207596483948992977854833 18155697362961744733391125)
                  ·
                    refine ⟨851048313888831784377709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18155697362961744733391125 851048313888831784377709)
                    ·
                      rfl

theorem cell23_4972232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 2, 6].length) (baseStart_4972232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4972232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4972232 prefixEnd_4972232 := by exact prefixLift 4972232
  have htrace : WordTrace (prefixWord ++ tailWord_4972232) baseStart_4972232 baseEnd_4972232 := by
    simpa [prefixWord, tailWord_4972232, baseEnd_4972232] using wordTrace_append hprefix tailTrace_4972232
  have hstable : (prefixWord ++ tailWord_4972232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4972232).length < 2 ^ (prefixWord ++ tailWord_4972232).sum := by decide
  have hdescent : baseEnd_4972232 < baseStart_4972232 := by decide
  rcases family_descends (prefixWord ++ tailWord_4972232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4972234 : List Nat := [3, 1, 2, 1, 6, 1, 2, 2, 1, 2, 2]
def baseStart_4972234 : Nat := 118140960795 + 4972234 * 2 ^ 59
def prefixEnd_4972234 : Nat := 4983230072969 + 3 ^ 40 * 4972234 * 2
def baseEnd_4972234 : Nat := 2553145968627804345308119

theorem tailTrace_4972234 : CollatzResearch.WordTrace tailWord_4972234 prefixEnd_4972234 2553145968627804345308119 := by
  unfold tailWord_4972234
  simp only [CollatzResearch.WordTrace]
  refine ⟨45338068167113220701210939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120901515112301921869895837 45338068167113220701210939)
  ·
    refine ⟨68007102250669831051816409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45338068167113220701210939 68007102250669831051816409)
    ·
      refine ⟨51005326688002373288862307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68007102250669831051816409 51005326688002373288862307)
      ·
        refine ⟨76507990032003559933293461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51005326688002373288862307 76507990032003559933293461)
        ·
          refine ⟨3586312032750166871873131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 76507990032003559933293461 3586312032750166871873131)
          ·
            refine ⟨5379468049125250307809697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3586312032750166871873131 5379468049125250307809697)
            ·
              refine ⟨4034601036843937730857273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5379468049125250307809697 4034601036843937730857273)
              ·
                refine ⟨3025950777632953298142955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4034601036843937730857273 3025950777632953298142955)
                ·
                  refine ⟨4538926166449429947214433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3025950777632953298142955 4538926166449429947214433)
                  ·
                    refine ⟨3404194624837072460410825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4538926166449429947214433 3404194624837072460410825)
                    ·
                      refine ⟨2553145968627804345308119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3404194624837072460410825 2553145968627804345308119)
                      ·
                        rfl

theorem cell23_4972234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 2, 2, 1, 2, 2].length) (baseStart_4972234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4972234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4972234 prefixEnd_4972234 := by exact prefixLift 4972234
  have htrace : WordTrace (prefixWord ++ tailWord_4972234) baseStart_4972234 baseEnd_4972234 := by
    simpa [prefixWord, tailWord_4972234, baseEnd_4972234] using wordTrace_append hprefix tailTrace_4972234
  have hstable : (prefixWord ++ tailWord_4972234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4972234).length < 2 ^ (prefixWord ++ tailWord_4972234).sum := by decide
  have hdescent : baseEnd_4972234 < baseStart_4972234 := by decide
  rcases family_descends (prefixWord ++ tailWord_4972234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4972279 : List Nat := [1, 1, 3, 1, 1, 1, 5, 5, 5]
def baseStart_4972279 : Nat := 118140960795 + 4972279 * 2 ^ 59
def prefixEnd_4972279 : Nat := 4983230072969 + 3 ^ 40 * 4972279 * 2
def baseEnd_4972279 : Nat := 283685452806361852138379

theorem tailTrace_4972279 : CollatzResearch.WordTrace tailWord_4972279 prefixEnd_4972279 283685452806361852138379 := by
  unfold tailWord_4972279
  simp only [CollatzResearch.WordTrace]
  refine ⟨181353913953289855490231891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120902609302193236993487927 181353913953289855490231891)
  ·
    refine ⟨272030870929934783235347837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181353913953289855490231891 272030870929934783235347837)
    ·
      refine ⟨102011576598725543713255439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 272030870929934783235347837 102011576598725543713255439)
      ·
        refine ⟨153017364898088315569883159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102011576598725543713255439 153017364898088315569883159)
        ·
          refine ⟨229526047347132473354824739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153017364898088315569883159 229526047347132473354824739)
          ·
            refine ⟨344289071020698710032237109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229526047347132473354824739 344289071020698710032237109)
            ·
              refine ⟨32277100408190504065522229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 344289071020698710032237109 32277100408190504065522229)
              ·
                refine ⟨3025978163267859756142709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32277100408190504065522229 3025978163267859756142709)
                ·
                  refine ⟨283685452806361852138379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3025978163267859756142709 283685452806361852138379)
                  ·
                    rfl

theorem cell23_4972279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 5, 5].length) (baseStart_4972279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4972279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4972279 prefixEnd_4972279 := by exact prefixLift 4972279
  have htrace : WordTrace (prefixWord ++ tailWord_4972279) baseStart_4972279 baseEnd_4972279 := by
    simpa [prefixWord, tailWord_4972279, baseEnd_4972279] using wordTrace_append hprefix tailTrace_4972279
  have hstable : (prefixWord ++ tailWord_4972279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4972279).length < 2 ^ (prefixWord ++ tailWord_4972279).sum := by decide
  have hdescent : baseEnd_4972279 < baseStart_4972279 := by decide
  rcases family_descends (prefixWord ++ tailWord_4972279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4972289 : List Nat := [1, 2, 4, 1, 1, 1, 3, 2, 2, 3, 3]
def baseStart_4972289 : Nat := 118140960795 + 4972289 * 2 ^ 59
def prefixEnd_4972289 : Nat := 4983230072969 + 3 ^ 40 * 4972289 * 2
def baseEnd_4972289 : Nat := 2553174210063801630120365

theorem tailTrace_4972289 : CollatzResearch.WordTrace tailWord_4972289 prefixEnd_4972289 2553174210063801630120365 := by
  unfold tailWord_4972289
  simp only [CollatzResearch.WordTrace]
  refine ⟨181354278683253627198095921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120902852455502418132063947 181354278683253627198095921)
  ·
    refine ⟨136015709012440220398571941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181354278683253627198095921 136015709012440220398571941)
    ·
      refine ⟨25502945439832541324732239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 136015709012440220398571941 25502945439832541324732239)
      ·
        refine ⟨38254418159748811987098359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25502945439832541324732239 38254418159748811987098359)
        ·
          refine ⟨57381627239623217980647539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38254418159748811987098359 57381627239623217980647539)
          ·
            refine ⟨86072440859434826970971309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57381627239623217980647539 86072440859434826970971309)
            ·
              refine ⟨32277165322288060114114241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86072440859434826970971309 32277165322288060114114241)
              ·
                refine ⟨24207873991716045085585681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32277165322288060114114241 24207873991716045085585681)
                ·
                  refine ⟨18155905493787033814189261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24207873991716045085585681 18155905493787033814189261)
                  ·
                    refine ⟨6808464560170137680320973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18155905493787033814189261 6808464560170137680320973)
                    ·
                      refine ⟨2553174210063801630120365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6808464560170137680320973 2553174210063801630120365)
                      ·
                        rfl

theorem cell23_4972289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 2, 3, 3].length) (baseStart_4972289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4972289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4972289 prefixEnd_4972289 := by exact prefixLift 4972289
  have htrace : WordTrace (prefixWord ++ tailWord_4972289) baseStart_4972289 baseEnd_4972289 := by
    simpa [prefixWord, tailWord_4972289, baseEnd_4972289] using wordTrace_append hprefix tailTrace_4972289
  have hstable : (prefixWord ++ tailWord_4972289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4972289).length < 2 ^ (prefixWord ++ tailWord_4972289).sum := by decide
  have hdescent : baseEnd_4972289 < baseStart_4972289 := by decide
  rcases family_descends (prefixWord ++ tailWord_4972289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4972299 : List Nat := [1, 1, 1, 1, 5, 1, 2, 1, 1, 7, 2]
def baseStart_4972299 : Nat := 118140960795 + 4972299 * 2 ^ 59
def prefixEnd_4972299 : Nat := 4983230072969 + 3 ^ 40 * 4972299 * 2
def baseEnd_4972299 : Nat := 2553179344870346590995319

theorem tailTrace_4972299 : CollatzResearch.WordTrace tailWord_4972299 prefixEnd_4972299 2553179344870346590995319 := by
  unfold tailWord_4972299
  simp only [CollatzResearch.WordTrace]
  refine ⟨181354643413217398905959951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120903095608811599270639967 181354643413217398905959951)
  ·
    refine ⟨272031965119826098358939927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181354643413217398905959951 272031965119826098358939927)
    ·
      refine ⟨408047947679739147538409891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272031965119826098358939927 408047947679739147538409891)
      ·
        refine ⟨612071921519608721307614837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 408047947679739147538409891 612071921519608721307614837)
        ·
          refine ⟨57381742642463317622588891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 612071921519608721307614837 57381742642463317622588891)
          ·
            refine ⟨86072613963694976433883337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57381742642463317622588891 86072613963694976433883337)
            ·
              refine ⟨64554460472771232325412503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86072613963694976433883337 64554460472771232325412503)
              ·
                refine ⟨96831690709156848488118755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64554460472771232325412503 96831690709156848488118755)
                ·
                  refine ⟨145247536063735272732178133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96831690709156848488118755 145247536063735272732178133)
                  ·
                    refine ⟨3404239126493795454660425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 145247536063735272732178133 3404239126493795454660425)
                    ·
                      refine ⟨2553179344870346590995319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3404239126493795454660425 2553179344870346590995319)
                      ·
                        rfl

theorem cell23_4972299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 7, 2].length) (baseStart_4972299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4972299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4972299 prefixEnd_4972299 := by exact prefixLift 4972299
  have htrace : WordTrace (prefixWord ++ tailWord_4972299) baseStart_4972299 baseEnd_4972299 := by
    simpa [prefixWord, tailWord_4972299, baseEnd_4972299] using wordTrace_append hprefix tailTrace_4972299
  have hstable : (prefixWord ++ tailWord_4972299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4972299).length < 2 ^ (prefixWord ++ tailWord_4972299).sum := by decide
  have hdescent : baseEnd_4972299 < baseStart_4972299 := by decide
  rcases family_descends (prefixWord ++ tailWord_4972299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4972301 : List Nat := [1, 7, 2, 1, 1, 1, 3, 1, 2, 1, 3]
def baseStart_4972301 : Nat := 118140960795 + 4972301 * 2 ^ 59
def prefixEnd_4972301 : Nat := 4983230072969 + 3 ^ 40 * 4972301 * 2
def baseEnd_4972301 : Nat := 2553180371831655583170311

theorem tailTrace_4972301 : CollatzResearch.WordTrace tailWord_4972301 prefixEnd_4972301 2553180371831655583170311 := by
  unfold tailWord_4972301
  simp only [CollatzResearch.WordTrace]
  refine ⟨181354716359210153247532757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120903144239473435498355171 181354716359210153247532757)
  ·
    refine ⟨4250501164668987966739049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 181354716359210153247532757 4250501164668987966739049)
    ·
      refine ⟨3187875873501740975054287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4250501164668987966739049 3187875873501740975054287)
      ·
        refine ⟨4781813810252611462581431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3187875873501740975054287 4781813810252611462581431)
        ·
          refine ⟨7172720715378917193872147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4781813810252611462581431 7172720715378917193872147)
          ·
            refine ⟨10759081073068375790808221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7172720715378917193872147 10759081073068375790808221)
            ·
              refine ⟨4034655402400640921553083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10759081073068375790808221 4034655402400640921553083)
              ·
                refine ⟨6051983103600961382329625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4034655402400640921553083 6051983103600961382329625)
                ·
                  refine ⟨4538987327700721036747219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6051983103600961382329625 4538987327700721036747219)
                  ·
                    refine ⟨6808480991551081555120829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4538987327700721036747219 6808480991551081555120829)
                    ·
                      refine ⟨2553180371831655583170311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6808480991551081555120829 2553180371831655583170311)
                      ·
                        rfl

theorem cell23_4972301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_4972301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4972301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4972301 prefixEnd_4972301 := by exact prefixLift 4972301
  have htrace : WordTrace (prefixWord ++ tailWord_4972301) baseStart_4972301 baseEnd_4972301 := by
    simpa [prefixWord, tailWord_4972301, baseEnd_4972301] using wordTrace_append hprefix tailTrace_4972301
  have hstable : (prefixWord ++ tailWord_4972301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4972301).length < 2 ^ (prefixWord ++ tailWord_4972301).sum := by decide
  have hdescent : baseEnd_4972301 < baseStart_4972301 := by decide
  rcases family_descends (prefixWord ++ tailWord_4972301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4972346 : List Nat := [3, 1, 1, 1, 5, 2, 1, 2, 2, 1, 4]
def baseStart_4972346 : Nat := 118140960795 + 4972346 * 2 ^ 59
def prefixEnd_4972346 : Nat := 4983230072969 + 3 ^ 40 * 4972346 * 2
def baseEnd_4972346 : Nat := 2553203478461107907107603

theorem tailTrace_4972346 : CollatzResearch.WordTrace tailWord_4972346 prefixEnd_4972346 2553203478461107907107603 := by
  unfold tailWord_4972346
  simp only [CollatzResearch.WordTrace]
  refine ⟨45339089411011781483230223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120904238429364750621947261 45339089411011781483230223)
  ·
    refine ⟨68008634116517672224845335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45339089411011781483230223 68008634116517672224845335)
    ·
      refine ⟨102012951174776508337268003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68008634116517672224845335 102012951174776508337268003)
      ·
        refine ⟨153019426762164762505902005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102012951174776508337268003 153019426762164762505902005)
        ·
          refine ⟨14345571258952946484928313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 153019426762164762505902005 14345571258952946484928313)
          ·
            refine ⟨10759178444214709863696235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14345571258952946484928313 10759178444214709863696235)
            ·
              refine ⟨16138767666322064795544353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10759178444214709863696235 16138767666322064795544353)
              ·
                refine ⟨12104075749741548596658265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16138767666322064795544353 12104075749741548596658265)
                ·
                  refine ⟨9078056812306161447493699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12104075749741548596658265 9078056812306161447493699)
                  ·
                    refine ⟨13617085218459242171240549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9078056812306161447493699 13617085218459242171240549)
                    ·
                      refine ⟨2553203478461107907107603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13617085218459242171240549 2553203478461107907107603)
                      ·
                        rfl

theorem cell23_4972346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 2, 2, 1, 4].length) (baseStart_4972346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4972346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4972346 prefixEnd_4972346 := by exact prefixLift 4972346
  have htrace : WordTrace (prefixWord ++ tailWord_4972346) baseStart_4972346 baseEnd_4972346 := by
    simpa [prefixWord, tailWord_4972346, baseEnd_4972346] using wordTrace_append hprefix tailTrace_4972346
  have hstable : (prefixWord ++ tailWord_4972346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4972346).length < 2 ^ (prefixWord ++ tailWord_4972346).sum := by decide
  have hdescent : baseEnd_4972346 < baseStart_4972346 := by decide
  rcases family_descends (prefixWord ++ tailWord_4972346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4972440 : List Nat := [2, 1, 2, 6, 1, 1, 1, 1, 1, 5, 2]
def baseStart_4972440 : Nat := 118140960795 + 4972440 * 2 ^ 59
def prefixEnd_4972440 : Nat := 4983230072969 + 3 ^ 40 * 4972440 * 2
def baseEnd_4972440 : Nat := 2553251745642630539332171

theorem tailTrace_4972440 : CollatzResearch.WordTrace tailWord_4972440 prefixEnd_4972440 2553251745642630539332171 := by
  unfold tailWord_4972440
  simp only [CollatzResearch.WordTrace]
  refine ⟨90679893052853289993421387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120906524070471053324561849 90679893052853289993421387)
  ·
    refine ⟨136019839579279934990132081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90679893052853289993421387 136019839579279934990132081)
    ·
      refine ⟨102014879684459951242599061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136019839579279934990132081 102014879684459951242599061)
      ·
        refine ⟨4781947485209060214496831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 102014879684459951242599061 4781947485209060214496831)
        ·
          refine ⟨7172921227813590321745247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4781947485209060214496831 7172921227813590321745247)
          ·
            refine ⟨10759381841720385482617871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7172921227813590321745247 10759381841720385482617871)
            ·
              refine ⟨16139072762580578223926807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10759381841720385482617871 16139072762580578223926807)
              ·
                refine ⟨24208609143870867335890211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16139072762580578223926807 24208609143870867335890211)
                ·
                  refine ⟨36312913715806301003835317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24208609143870867335890211 36312913715806301003835317)
                  ·
                    refine ⟨3404335660856840719109561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36312913715806301003835317 3404335660856840719109561)
                    ·
                      refine ⟨2553251745642630539332171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3404335660856840719109561 2553251745642630539332171)
                      ·
                        rfl

theorem cell23_4972440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_4972440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4972440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4972440 prefixEnd_4972440 := by exact prefixLift 4972440
  have htrace : WordTrace (prefixWord ++ tailWord_4972440) baseStart_4972440 baseEnd_4972440 := by
    simpa [prefixWord, tailWord_4972440, baseEnd_4972440] using wordTrace_append hprefix tailTrace_4972440
  have hstable : (prefixWord ++ tailWord_4972440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4972440).length < 2 ^ (prefixWord ++ tailWord_4972440).sum := by decide
  have hdescent : baseEnd_4972440 < baseStart_4972440 := by decide
  rcases family_descends (prefixWord ++ tailWord_4972440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4972447 : List Nat := [1, 1, 2, 5, 3, 1, 2, 3, 1, 1, 3]
def baseStart_4972447 : Nat := 118140960795 + 4972447 * 2 ^ 59
def prefixEnd_4972447 : Nat := 4983230072969 + 3 ^ 40 * 4972447 * 2
def baseEnd_4972447 : Nat := 2553255340007212011944639

theorem tailTrace_4972447 : CollatzResearch.WordTrace tailWord_4972447 prefixEnd_4972447 2553255340007212011944639 := by
  unfold tailWord_4972447
  simp only [CollatzResearch.WordTrace]
  refine ⟨181360041416681220182347595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120906694277787480121565063 181360041416681220182347595)
  ·
    refine ⟨272040062125021830273521393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181360041416681220182347595 272040062125021830273521393)
    ·
      refine ⟨204030046593766372705141045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 272040062125021830273521393 204030046593766372705141045)
      ·
        refine ⟨19127816868165597441106973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 204030046593766372705141045 19127816868165597441106973)
        ·
          refine ⟨7172931325562099040415115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19127816868165597441106973 7172931325562099040415115)
          ·
            refine ⟨10759396988343148560622673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7172931325562099040415115 10759396988343148560622673)
            ·
              refine ⟨8069547741257361420467005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10759396988343148560622673 8069547741257361420467005)
              ·
                refine ⟨3026080402971510532675127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8069547741257361420467005 3026080402971510532675127)
                ·
                  refine ⟨4539120604457265799012691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3026080402971510532675127 4539120604457265799012691)
                  ·
                    refine ⟨6808680906685898698519037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4539120604457265799012691 6808680906685898698519037)
                    ·
                      refine ⟨2553255340007212011944639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6808680906685898698519037 2553255340007212011944639)
                      ·
                        rfl

theorem cell23_4972447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 3, 1, 1, 3].length) (baseStart_4972447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4972447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4972447 prefixEnd_4972447 := by exact prefixLift 4972447
  have htrace : WordTrace (prefixWord ++ tailWord_4972447) baseStart_4972447 baseEnd_4972447 := by
    simpa [prefixWord, tailWord_4972447, baseEnd_4972447] using wordTrace_append hprefix tailTrace_4972447
  have hstable : (prefixWord ++ tailWord_4972447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4972447).length < 2 ^ (prefixWord ++ tailWord_4972447).sum := by decide
  have hdescent : baseEnd_4972447 < baseStart_4972447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4972447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4972537 : List Nat := [1, 2, 1, 3, 1, 6, 2, 1, 2, 1, 3]
def baseStart_4972537 : Nat := 118140960795 + 4972537 * 2 ^ 59
def prefixEnd_4972537 : Nat := 4983230072969 + 3 ^ 40 * 4972537 * 2
def baseEnd_4972537 : Nat := 2553301553266116659819225

theorem tailTrace_4972537 : CollatzResearch.WordTrace tailWord_4972537 prefixEnd_4972537 2553301553266116659819225 := by
  unfold tailWord_4972537
  simp only [CollatzResearch.WordTrace]
  refine ⟨181363323986355165553123865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120908882657570110368749243 181363323986355165553123865)
  ·
    refine ⟨136022492989766374164842899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181363323986355165553123865 136022492989766374164842899)
    ·
      refine ⟨204033739484649561247264349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136022492989766374164842899 204033739484649561247264349)
      ·
        refine ⟨76512652306743585467724131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 204033739484649561247264349 76512652306743585467724131)
        ·
          refine ⟨114768978460115378201586197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76512652306743585467724131 114768978460115378201586197)
          ·
            refine ⟨5379795865317908353199353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 114768978460115378201586197 5379795865317908353199353)
            ·
              refine ⟨4034846898988431264899515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5379795865317908353199353 4034846898988431264899515)
              ·
                refine ⟨6052270348482646897349273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4034846898988431264899515 6052270348482646897349273)
                ·
                  refine ⟨4539202761361985173011955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6052270348482646897349273 4539202761361985173011955)
                  ·
                    refine ⟨6808804142042977759517933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4539202761361985173011955 6808804142042977759517933)
                    ·
                      refine ⟨2553301553266116659819225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6808804142042977759517933 2553301553266116659819225)
                      ·
                        rfl

theorem cell23_4972537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 2, 1, 2, 1, 3].length) (baseStart_4972537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4972537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4972537 prefixEnd_4972537 := by exact prefixLift 4972537
  have htrace : WordTrace (prefixWord ++ tailWord_4972537) baseStart_4972537 baseEnd_4972537 := by
    simpa [prefixWord, tailWord_4972537, baseEnd_4972537] using wordTrace_append hprefix tailTrace_4972537
  have hstable : (prefixWord ++ tailWord_4972537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4972537).length < 2 ^ (prefixWord ++ tailWord_4972537).sum := by decide
  have hdescent : baseEnd_4972537 < baseStart_4972537 := by decide
  rcases family_descends (prefixWord ++ tailWord_4972537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4972593 : List Nat := [1, 2, 2, 3, 1, 4, 1, 1, 2, 3, 3]
def baseStart_4972593 : Nat := 118140960795 + 4972593 * 2 ^ 59
def prefixEnd_4972593 : Nat := 4983230072969 + 3 ^ 40 * 4972593 * 2
def baseEnd_4972593 : Nat := 2553330308182768440718967

theorem tailTrace_4972593 : CollatzResearch.WordTrace tailWord_4972593 prefixEnd_4972593 2553330308182768440718967 := by
  unfold tailWord_4972593
  simp only [CollatzResearch.WordTrace]
  refine ⟨181365366474152287117162433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120910244316101524744774955 181365366474152287117162433)
  ·
    refine ⟨136024024855614215337871825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181365366474152287117162433 136024024855614215337871825)
    ·
      refine ⟨102018018641710661503403869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136024024855614215337871825 102018018641710661503403869)
      ·
        refine ⟨38256756990641498063776451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102018018641710661503403869 38256756990641498063776451)
        ·
          refine ⟨57385135485962247095664677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38256756990641498063776451 57385135485962247095664677)
          ·
            refine ⟨10759712903617921330437127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57385135485962247095664677 10759712903617921330437127)
            ·
              refine ⟨16139569355426881995655691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10759712903617921330437127 16139569355426881995655691)
              ·
                refine ⟨24209354033140322993483537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16139569355426881995655691 24209354033140322993483537)
                ·
                  refine ⟨18157015524855242245112653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24209354033140322993483537 18157015524855242245112653)
                  ·
                    refine ⟨6808880821820715841917245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18157015524855242245112653 6808880821820715841917245)
                    ·
                      refine ⟨2553330308182768440718967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6808880821820715841917245 2553330308182768440718967)
                      ·
                        rfl

theorem cell23_4972593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 2, 3, 3].length) (baseStart_4972593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4972593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4972593 prefixEnd_4972593 := by exact prefixLift 4972593
  have htrace : WordTrace (prefixWord ++ tailWord_4972593) baseStart_4972593 baseEnd_4972593 := by
    simpa [prefixWord, tailWord_4972593, baseEnd_4972593] using wordTrace_append hprefix tailTrace_4972593
  have hstable : (prefixWord ++ tailWord_4972593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4972593).length < 2 ^ (prefixWord ++ tailWord_4972593).sum := by decide
  have hdescent : baseEnd_4972593 < baseStart_4972593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4972593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4972633 : List Nat := [1, 2, 1, 2, 2, 1, 3, 1, 4, 4, 2]
def baseStart_4972633 : Nat := 118140960795 + 4972633 * 2 ^ 59
def prefixEnd_4972633 : Nat := 4983230072969 + 3 ^ 40 * 4972633 * 2
def baseEnd_4972633 : Nat := 2553350847408948284218783

theorem tailTrace_4972633 : CollatzResearch.WordTrace tailWord_4972633 prefixEnd_4972633 2553350847408948284218783 := by
  unfold tailWord_4972633
  simp only [CollatzResearch.WordTrace]
  refine ⟨181366825394007373948618553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120911216929338249299079035 181366825394007373948618553)
  ·
    refine ⟨136025119045505530461463915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181366825394007373948618553 136025119045505530461463915)
    ·
      refine ⟨204037678568258295692195873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136025119045505530461463915 204037678568258295692195873)
      ·
        refine ⟨153028258926193721769146905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204037678568258295692195873 153028258926193721769146905)
        ·
          refine ⟨114771194194645291326860179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153028258926193721769146905 114771194194645291326860179)
          ·
            refine ⟨172156791291967936990290269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114771194194645291326860179 172156791291967936990290269)
            ·
              refine ⟨64558796734487976371358851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 172156791291967936990290269 64558796734487976371358851)
              ·
                refine ⟨96838195101731964557038277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64558796734487976371358851 96838195101731964557038277)
                ·
                  refine ⟨18157161581574743354444677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 96838195101731964557038277 18157161581574743354444677)
                  ·
                    refine ⟨3404467796545264378958377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18157161581574743354444677 3404467796545264378958377)
                    ·
                      refine ⟨2553350847408948284218783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3404467796545264378958377 2553350847408948284218783)
                      ·
                        rfl

theorem cell23_4972633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 4, 4, 2].length) (baseStart_4972633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4972633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4972633 prefixEnd_4972633 := by exact prefixLift 4972633
  have htrace : WordTrace (prefixWord ++ tailWord_4972633) baseStart_4972633 baseEnd_4972633 := by
    simpa [prefixWord, tailWord_4972633, baseEnd_4972633] using wordTrace_append hprefix tailTrace_4972633
  have hstable : (prefixWord ++ tailWord_4972633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4972633).length < 2 ^ (prefixWord ++ tailWord_4972633).sum := by decide
  have hdescent : baseEnd_4972633 < baseStart_4972633 := by decide
  rcases family_descends (prefixWord ++ tailWord_4972633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4972643 : List Nat := [1, 1, 1, 5, 1, 1, 3, 3, 3, 4]
def baseStart_4972643 : Nat := 118140960795 + 4972643 * 2 ^ 59
def prefixEnd_4972643 : Nat := 4983230072969 + 3 ^ 40 * 4972643 * 2
def baseEnd_4972643 : Nat := 851118660738497748364579

theorem tailTrace_4972643 : CollatzResearch.WordTrace tailWord_4972643 prefixEnd_4972643 851118660738497748364579 := by
  unfold tailWord_4972643
  simp only [CollatzResearch.WordTrace]
  refine ⟨181367190123971145656482583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120911460082647430437655055 181367190123971145656482583)
  ·
    refine ⟨272050785185956718484723875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181367190123971145656482583 272050785185956718484723875)
    ·
      refine ⟨408076177778935077727085813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272050785185956718484723875 408076177778935077727085813)
      ·
        refine ⟨38257141666775163536914295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 408076177778935077727085813 38257141666775163536914295)
        ·
          refine ⟨57385712500162745305371443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38257141666775163536914295 57385712500162745305371443)
          ·
            refine ⟨86078568750244117958057165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57385712500162745305371443 86078568750244117958057165)
            ·
              refine ⟨32279463281341544234271437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86078568750244117958057165 32279463281341544234271437)
              ·
                refine ⟨12104798730503079087851789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32279463281341544234271437 12104798730503079087851789)
                ·
                  refine ⟨4539299523938654657944421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12104798730503079087851789 4539299523938654657944421)
                  ·
                    refine ⟨851118660738497748364579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4539299523938654657944421 851118660738497748364579)
                    ·
                      rfl

theorem cell23_4972643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 3, 3, 4].length) (baseStart_4972643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4972643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4972643 prefixEnd_4972643 := by exact prefixLift 4972643
  have htrace : WordTrace (prefixWord ++ tailWord_4972643) baseStart_4972643 baseEnd_4972643 := by
    simpa [prefixWord, tailWord_4972643, baseEnd_4972643] using wordTrace_append hprefix tailTrace_4972643
  have hstable : (prefixWord ++ tailWord_4972643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4972643).length < 2 ^ (prefixWord ++ tailWord_4972643).sum := by decide
  have hdescent : baseEnd_4972643 < baseStart_4972643 := by decide
  rcases family_descends (prefixWord ++ tailWord_4972643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4972653 : List Nat := [1, 5, 1, 1, 2, 1, 1, 1, 3, 4, 3]
def baseStart_4972653 : Nat := 118140960795 + 4972653 * 2 ^ 59
def prefixEnd_4972653 : Nat := 4983230072969 + 3 ^ 40 * 4972653 * 2
def baseEnd_4972653 : Nat := 2553361117022038205968691

theorem tailTrace_4972653 : CollatzResearch.WordTrace tailWord_4972653 prefixEnd_4972653 2553361117022038205968691 := by
  unfold tailWord_4972653
  simp only [CollatzResearch.WordTrace]
  refine ⟨181367554853934917364346613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120911703235956611576231075 181367554853934917364346613)
  ·
    refine ⟨17003208267556398502907495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 181367554853934917364346613 17003208267556398502907495)
    ·
      refine ⟨25504812401334597754361243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17003208267556398502907495 25504812401334597754361243)
      ·
        refine ⟨38257218602001896631541865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25504812401334597754361243 38257218602001896631541865)
        ·
          refine ⟨28692913951501422473656399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38257218602001896631541865 28692913951501422473656399)
          ·
            refine ⟨43039370927252133710484599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28692913951501422473656399 43039370927252133710484599)
            ·
              refine ⟨64559056390878200565726899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43039370927252133710484599 64559056390878200565726899)
              ·
                refine ⟨96838584586317300848590349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64559056390878200565726899 96838584586317300848590349)
                ·
                  refine ⟨36314469219868987818221381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96838584586317300848590349 36314469219868987818221381)
                  ·
                    refine ⟨6808962978725435215916509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36314469219868987818221381 6808962978725435215916509)
                    ·
                      refine ⟨2553361117022038205968691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6808962978725435215916509 2553361117022038205968691)
                      ·
                        rfl

theorem cell23_4972653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 4, 3].length) (baseStart_4972653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4972653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4972653 prefixEnd_4972653 := by exact prefixLift 4972653
  have htrace : WordTrace (prefixWord ++ tailWord_4972653) baseStart_4972653 baseEnd_4972653 := by
    simpa [prefixWord, tailWord_4972653, baseEnd_4972653] using wordTrace_append hprefix tailTrace_4972653
  have hstable : (prefixWord ++ tailWord_4972653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4972653).length < 2 ^ (prefixWord ++ tailWord_4972653).sum := by decide
  have hdescent : baseEnd_4972653 < baseStart_4972653 := by decide
  rcases family_descends (prefixWord ++ tailWord_4972653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4972677 : List Nat := [1, 3, 1, 1, 5, 1, 3, 3, 1, 4]
def baseStart_4972677 : Nat := 118140960795 + 4972677 * 2 ^ 59
def prefixEnd_4972677 : Nat := 4983230072969 + 3 ^ 40 * 4972677 * 2
def baseEnd_4972677 : Nat := 851124480185915370689527

theorem tailTrace_4972677 : CollatzResearch.WordTrace tailWord_4972677 prefixEnd_4972677 851124480185915370689527 := by
  unfold tailWord_4972677
  simp only [CollatzResearch.WordTrace]
  refine ⟨181368430205847969463220285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120912286803898646308813523 181368430205847969463220285)
  ·
    refine ⟨68013161327192988548707607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181368430205847969463220285 68013161327192988548707607)
    ·
      refine ⟨102019741990789482823061411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68013161327192988548707607 102019741990789482823061411)
      ·
        refine ⟨153029612986184224234592117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102019741990789482823061411 153029612986184224234592117)
        ·
          refine ⟨14346526217454771021993011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 153029612986184224234592117 14346526217454771021993011)
          ·
            refine ⟨21519789326182156532989517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14346526217454771021993011 21519789326182156532989517)
            ·
              refine ⟨8069920997318308699871069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21519789326182156532989517 8069920997318308699871069)
              ·
                refine ⟨3026220373994365762451651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8069920997318308699871069 3026220373994365762451651)
                ·
                  refine ⟨4539330560991548643677477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3026220373994365762451651 4539330560991548643677477)
                  ·
                    refine ⟨851124480185915370689527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4539330560991548643677477 851124480185915370689527)
                    ·
                      rfl

theorem cell23_4972677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 3, 1, 4].length) (baseStart_4972677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4972677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4972677 prefixEnd_4972677 := by exact prefixLift 4972677
  have htrace : WordTrace (prefixWord ++ tailWord_4972677) baseStart_4972677 baseEnd_4972677 := by
    simpa [prefixWord, tailWord_4972677, baseEnd_4972677] using wordTrace_append hprefix tailTrace_4972677
  have hstable : (prefixWord ++ tailWord_4972677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4972677).length < 2 ^ (prefixWord ++ tailWord_4972677).sum := by decide
  have hdescent : baseEnd_4972677 < baseStart_4972677 := by decide
  rcases family_descends (prefixWord ++ tailWord_4972677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4972727 : List Nat := [1, 1, 3, 1, 4, 3, 2, 1, 2, 3, 2]
def baseStart_4972727 : Nat := 118140960795 + 4972727 * 2 ^ 59
def prefixEnd_4972727 : Nat := 4983230072969 + 3 ^ 40 * 4972727 * 2
def baseEnd_4972727 : Nat := 2553399114590470916443351

theorem tailTrace_4972727 : CollatzResearch.WordTrace tailWord_4972727 prefixEnd_4972727 2553399114590470916443351 := by
  unfold tailWord_4972727
  simp only [CollatzResearch.WordTrace]
  refine ⟨181370253855666828002540435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120913502570444552001693623 181370253855666828002540435)
  ·
    refine ⟨272055380783500242003810653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181370253855666828002540435 272055380783500242003810653)
    ·
      refine ⟨102020767793812590751428995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 272055380783500242003810653 102020767793812590751428995)
      ·
        refine ⟨153031151690718886127143493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102020767793812590751428995 153031151690718886127143493)
        ·
          refine ⟨28693340942009791148839405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 153031151690718886127143493 28693340942009791148839405)
          ·
            refine ⟨10760002853253671680814777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28693340942009791148839405 10760002853253671680814777)
            ·
              refine ⟨8070002139940253760611083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10760002853253671680814777 8070002139940253760611083)
              ·
                refine ⟨12105003209910380640916625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8070002139940253760611083 12105003209910380640916625)
                ·
                  refine ⟨9078752407432785480687469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12105003209910380640916625 9078752407432785480687469)
                  ·
                    refine ⟨3404532152787294555257801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9078752407432785480687469 3404532152787294555257801)
                    ·
                      refine ⟨2553399114590470916443351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3404532152787294555257801 2553399114590470916443351)
                      ·
                        rfl

theorem cell23_4972727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 1, 2, 3, 2].length) (baseStart_4972727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4972727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4972727 prefixEnd_4972727 := by exact prefixLift 4972727
  have htrace : WordTrace (prefixWord ++ tailWord_4972727) baseStart_4972727 baseEnd_4972727 := by
    simpa [prefixWord, tailWord_4972727, baseEnd_4972727] using wordTrace_append hprefix tailTrace_4972727
  have hstable : (prefixWord ++ tailWord_4972727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4972727).length < 2 ^ (prefixWord ++ tailWord_4972727).sum := by decide
  have hdescent : baseEnd_4972727 < baseStart_4972727 := by decide
  rcases family_descends (prefixWord ++ tailWord_4972727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4972760 : List Nat := [2, 1, 2, 2, 4, 1, 1, 2, 3, 2, 3]
def baseStart_4972760 : Nat := 118140960795 + 4972760 * 2 ^ 59
def prefixEnd_4972760 : Nat := 4983230072969 + 3 ^ 40 * 4972760 * 2
def baseEnd_4972760 : Nat := 2553416059452069287330699

theorem tailTrace_4972760 : CollatzResearch.WordTrace tailWord_4972760 prefixEnd_4972760 2553416059452069287330699 := by
  unfold tailWord_4972760
  simp only [CollatzResearch.WordTrace]
  refine ⟨90685728732273637319245867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120914304976364849758994489 90685728732273637319245867)
  ·
    refine ⟨136028593098410455978868801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90685728732273637319245867 136028593098410455978868801)
    ·
      refine ⟨102021444823807841984151601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136028593098410455978868801 102021444823807841984151601)
      ·
        refine ⟨76516083617855881488113701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102021444823807841984151601 76516083617855881488113701)
        ·
          refine ⟨14346765678347977779021319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76516083617855881488113701 14346765678347977779021319)
          ·
            refine ⟨21520148517521966668531979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14346765678347977779021319 21520148517521966668531979)
            ·
              refine ⟨32280222776282950002797969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21520148517521966668531979 32280222776282950002797969)
              ·
                refine ⟨24210167082212212502098477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32280222776282950002797969 24210167082212212502098477)
                ·
                  refine ⟨9078812655829579688286929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24210167082212212502098477 9078812655829579688286929)
                  ·
                    refine ⟨6809109491872184766215197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9078812655829579688286929 6809109491872184766215197)
                    ·
                      refine ⟨2553416059452069287330699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6809109491872184766215197 2553416059452069287330699)
                      ·
                        rfl

theorem cell23_4972760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 3, 2, 3].length) (baseStart_4972760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4972760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4972760 prefixEnd_4972760 := by exact prefixLift 4972760
  have htrace : WordTrace (prefixWord ++ tailWord_4972760) baseStart_4972760 baseEnd_4972760 := by
    simpa [prefixWord, tailWord_4972760, baseEnd_4972760] using wordTrace_append hprefix tailTrace_4972760
  have hstable : (prefixWord ++ tailWord_4972760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4972760).length < 2 ^ (prefixWord ++ tailWord_4972760).sum := by decide
  have hdescent : baseEnd_4972760 < baseStart_4972760 := by decide
  rcases family_descends (prefixWord ++ tailWord_4972760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4972794 : List Nat := [3, 1, 1, 1, 1, 7, 2, 1, 1, 2, 3]
def baseStart_4972794 : Nat := 118140960795 + 4972794 * 2 ^ 59
def prefixEnd_4972794 : Nat := 4983230072969 + 3 ^ 40 * 4972794 * 2
def baseEnd_4972794 : Nat := 2553433517794322154305543

theorem tailTrace_4972794 : CollatzResearch.WordTrace tailWord_4972794 prefixEnd_4972794 2553433517794322154305543 := by
  unfold tailWord_4972794
  simp only [CollatzResearch.WordTrace]
  refine ⟨45343174386606024611307359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120915131697616065630152957 45343174386606024611307359)
  ·
    refine ⟨68014761579909036916961039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45343174386606024611307359 68014761579909036916961039)
    ·
      refine ⟨102022142369863555375441559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68014761579909036916961039 102022142369863555375441559)
      ·
        refine ⟨153033213554795333063162339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102022142369863555375441559 153033213554795333063162339)
        ·
          refine ⟨229549820332192999594743509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153033213554795333063162339 229549820332192999594743509)
          ·
            refine ⟨5380073914035773428001801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 229549820332192999594743509 5380073914035773428001801)
            ·
              refine ⟨4035055435526830071001351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5380073914035773428001801 4035055435526830071001351)
              ·
                refine ⟨6052583153290245106502027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4035055435526830071001351 6052583153290245106502027)
                ·
                  refine ⟨9078874729935367659753041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6052583153290245106502027 9078874729935367659753041)
                  ·
                    refine ⟨6809156047451525744814781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9078874729935367659753041 6809156047451525744814781)
                    ·
                      refine ⟨2553433517794322154305543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6809156047451525744814781 2553433517794322154305543)
                      ·
                        rfl

theorem cell23_4972794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 2, 1, 1, 2, 3].length) (baseStart_4972794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4972794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4972794 prefixEnd_4972794 := by exact prefixLift 4972794
  have htrace : WordTrace (prefixWord ++ tailWord_4972794) baseStart_4972794 baseEnd_4972794 := by
    simpa [prefixWord, tailWord_4972794, baseEnd_4972794] using wordTrace_append hprefix tailTrace_4972794
  have hstable : (prefixWord ++ tailWord_4972794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4972794).length < 2 ^ (prefixWord ++ tailWord_4972794).sum := by decide
  have hdescent : baseEnd_4972794 < baseStart_4972794 := by decide
  rcases family_descends (prefixWord ++ tailWord_4972794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4972824 : List Nat := [2, 1, 2, 3, 1, 2, 5, 1, 2, 1, 3]
def baseStart_4972824 : Nat := 118140960795 + 4972824 * 2 ^ 59
def prefixEnd_4972824 : Nat := 4983230072969 + 3 ^ 40 * 4972824 * 2
def baseEnd_4972824 : Nat := 2553448922213957036930405

theorem tailTrace_4972824 : CollatzResearch.WordTrace tailWord_4972824 prefixEnd_4972824 2553448922213957036930405 := by
  unfold tailWord_4972824
  simp only [CollatzResearch.WordTrace]
  refine ⟨90686895868157706784410763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120915861157543609045881017 90686895868157706784410763)
  ·
    refine ⟨136030343802236560176616145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90686895868157706784410763 136030343802236560176616145)
    ·
      refine ⟨102022757851677420132462109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136030343802236560176616145 102022757851677420132462109)
      ·
        refine ⟨38258534194379032549673291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102022757851677420132462109 38258534194379032549673291)
        ·
          refine ⟨57387801291568548824509937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38258534194379032549673291 57387801291568548824509937)
          ·
            refine ⟨43040850968676411618382453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57387801291568548824509937 43040850968676411618382453)
            ·
              refine ⟨4035079778313413589223355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43040850968676411618382453 4035079778313413589223355)
              ·
                refine ⟨6052619667470120383835033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4035079778313413589223355 6052619667470120383835033)
                ·
                  refine ⟨4539464750602590287876275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6052619667470120383835033 4539464750602590287876275)
                  ·
                    refine ⟨6809197125903885431814413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4539464750602590287876275 6809197125903885431814413)
                    ·
                      refine ⟨2553448922213957036930405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6809197125903885431814413 2553448922213957036930405)
                      ·
                        rfl

theorem cell23_4972824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 5, 1, 2, 1, 3].length) (baseStart_4972824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4972824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4972824 prefixEnd_4972824 := by exact prefixLift 4972824
  have htrace : WordTrace (prefixWord ++ tailWord_4972824) baseStart_4972824 baseEnd_4972824 := by
    simpa [prefixWord, tailWord_4972824, baseEnd_4972824] using wordTrace_append hprefix tailTrace_4972824
  have hstable : (prefixWord ++ tailWord_4972824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4972824).length < 2 ^ (prefixWord ++ tailWord_4972824).sum := by decide
  have hdescent : baseEnd_4972824 < baseStart_4972824 := by decide
  rcases family_descends (prefixWord ++ tailWord_4972824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4972834 : List Nat := [3, 3, 1, 1, 3, 1, 1, 4, 1, 3, 2]
def baseStart_4972834 : Nat := 118140960795 + 4972834 * 2 ^ 59
def prefixEnd_4972834 : Nat := 4983230072969 + 3 ^ 40 * 4972834 * 2
def baseEnd_4972834 : Nat := 2553454057020501997805359

theorem tailTrace_4972834 : CollatzResearch.WordTrace tailWord_4972834 prefixEnd_4972834 2553454057020501997805359 := by
  unfold tailWord_4972834
  simp only [CollatzResearch.WordTrace]
  refine ⟨45343539116569796319171389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120916104310852790184457037 45343539116569796319171389)
  ·
    refine ⟨17003827168713673619689271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45343539116569796319171389 17003827168713673619689271)
    ·
      refine ⟨25505740753070510429533907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17003827168713673619689271 25505740753070510429533907)
      ·
        refine ⟨38258611129605765644300861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25505740753070510429533907 38258611129605765644300861)
        ·
          refine ⟨14346979173602162116612823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38258611129605765644300861 14346979173602162116612823)
          ·
            refine ⟨21520468760403243174919235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14346979173602162116612823 21520468760403243174919235)
            ·
              refine ⟨32280703140604864762378853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21520468760403243174919235 32280703140604864762378853)
              ·
                refine ⟨6052631838863412142946035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32280703140604864762378853 6052631838863412142946035)
                ·
                  refine ⟨9078947758295118214419053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6052631838863412142946035 9078947758295118214419053)
                  ·
                    refine ⟨3404605409360669330407145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9078947758295118214419053 3404605409360669330407145)
                    ·
                      refine ⟨2553454057020501997805359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3404605409360669330407145 2553454057020501997805359)
                      ·
                        rfl

theorem cell23_4972834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 4, 1, 3, 2].length) (baseStart_4972834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4972834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4972834 prefixEnd_4972834 := by exact prefixLift 4972834
  have htrace : WordTrace (prefixWord ++ tailWord_4972834) baseStart_4972834 baseEnd_4972834 := by
    simpa [prefixWord, tailWord_4972834, baseEnd_4972834] using wordTrace_append hprefix tailTrace_4972834
  have hstable : (prefixWord ++ tailWord_4972834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4972834).length < 2 ^ (prefixWord ++ tailWord_4972834).sum := by decide
  have hdescent : baseEnd_4972834 < baseStart_4972834 := by decide
  rcases family_descends (prefixWord ++ tailWord_4972834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4972847 : List Nat := [1, 1, 2, 1, 2, 1, 5, 2, 4, 2, 2]
def baseStart_4972847 : Nat := 118140960795 + 4972847 * 2 ^ 59
def prefixEnd_4972847 : Nat := 4983230072969 + 3 ^ 40 * 4972847 * 2
def baseEnd_4972847 : Nat := 2553460732269010446942799

theorem tailTrace_4972847 : CollatzResearch.WordTrace tailWord_4972847 prefixEnd_4972847 2553460732269010446942799 := by
  unfold tailWord_4972847
  simp only [CollatzResearch.WordTrace]
  refine ⟨181374630615232088496908795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120916420410154725664605863 181374630615232088496908795)
  ·
    refine ⟨272061945922848132745363193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181374630615232088496908795 272061945922848132745363193)
    ·
      refine ⟨204046459442136099559022395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 272061945922848132745363193 204046459442136099559022395)
      ·
        refine ⟨306069689163204149338533593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204046459442136099559022395 306069689163204149338533593)
        ·
          refine ⟨229552266872403112003900195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 306069689163204149338533593 229552266872403112003900195)
          ·
            refine ⟨344328400308604668005850293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229552266872403112003900195 344328400308604668005850293)
            ·
              refine ⟨32280787528931687625548465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 344328400308604668005850293 32280787528931687625548465)
              ·
                refine ⟨24210590646698765719161349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32280787528931687625548465 24210590646698765719161349)
                ·
                  refine ⟨4539485746256018572342753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24210590646698765719161349 4539485746256018572342753)
                  ·
                    refine ⟨3404614309692013929257065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4539485746256018572342753 3404614309692013929257065)
                    ·
                      refine ⟨2553460732269010446942799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3404614309692013929257065 2553460732269010446942799)
                      ·
                        rfl

theorem cell23_4972847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 4, 2, 2].length) (baseStart_4972847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4972847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4972847 prefixEnd_4972847 := by exact prefixLift 4972847
  have htrace : WordTrace (prefixWord ++ tailWord_4972847) baseStart_4972847 baseEnd_4972847 := by
    simpa [prefixWord, tailWord_4972847, baseEnd_4972847] using wordTrace_append hprefix tailTrace_4972847
  have hstable : (prefixWord ++ tailWord_4972847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4972847).length < 2 ^ (prefixWord ++ tailWord_4972847).sum := by decide
  have hdescent : baseEnd_4972847 < baseStart_4972847 := by decide
  rcases family_descends (prefixWord ++ tailWord_4972847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4972863 : List Nat := [1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 7]
def baseStart_4972863 : Nat := 118140960795 + 4972863 * 2 ^ 59
def prefixEnd_4972863 : Nat := 4983230072969 + 3 ^ 40 * 4972863 * 2
def baseEnd_4972863 : Nat := 2553468947959482384342725

theorem tailTrace_4972863 : CollatzResearch.WordTrace tailWord_4972863 prefixEnd_4972863 2553468947959482384342725 := by
  unfold tailWord_4972863
  simp only [CollatzResearch.WordTrace]
  refine ⟨181375214183174123229491243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120916809455449415486327495 181375214183174123229491243)
  ·
    refine ⟨272062821274761184844236865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181375214183174123229491243 272062821274761184844236865)
    ·
      refine ⟨204047115956070888633177649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 272062821274761184844236865 204047115956070888633177649)
      ·
        refine ⟨153035336967053166474883237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204047115956070888633177649 153035336967053166474883237)
        ·
          refine ⟨28694125681322468714040607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 153035336967053166474883237 28694125681322468714040607)
          ·
            refine ⟨43041188521983703071060911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28694125681322468714040607 43041188521983703071060911)
            ·
              refine ⟨64561782782975554606591367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43041188521983703071060911 64561782782975554606591367)
              ·
                refine ⟨96842674174463331909887051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64561782782975554606591367 96842674174463331909887051)
                ·
                  refine ⟨145264011261694997864830577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96842674174463331909887051 145264011261694997864830577)
                  ·
                    refine ⟨108948008446271248398622933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 145264011261694997864830577 108948008446271248398622933)
                    ·
                      refine ⟨2553468947959482384342725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 108948008446271248398622933 2553468947959482384342725)
                      ·
                        rfl

theorem cell23_4972863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 7].length) (baseStart_4972863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4972863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4972863 prefixEnd_4972863 := by exact prefixLift 4972863
  have htrace : WordTrace (prefixWord ++ tailWord_4972863) baseStart_4972863 baseEnd_4972863 := by
    simpa [prefixWord, tailWord_4972863, baseEnd_4972863] using wordTrace_append hprefix tailTrace_4972863
  have hstable : (prefixWord ++ tailWord_4972863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4972863).length < 2 ^ (prefixWord ++ tailWord_4972863).sum := by decide
  have hdescent : baseEnd_4972863 < baseStart_4972863 := by decide
  rcases family_descends (prefixWord ++ tailWord_4972863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4972881 : List Nat := [1, 2, 2, 1, 4, 2, 4, 1, 2, 2, 2]
def baseStart_4972881 : Nat := 118140960795 + 4972881 * 2 ^ 59
def prefixEnd_4972881 : Nat := 4983230072969 + 3 ^ 40 * 4972881 * 2
def baseEnd_4972881 : Nat := 2553478190611263313917643

theorem tailTrace_4972881 : CollatzResearch.WordTrace tailWord_4972881 prefixEnd_4972881 2553478190611263313917643 := by
  unfold tailWord_4972881
  simp only [CollatzResearch.WordTrace]
  refine ⟨181375870697108912303646497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120917247131405941535764331 181375870697108912303646497)
  ·
    refine ⟨136031903022831684227734873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181375870697108912303646497 136031903022831684227734873)
    ·
      refine ⟨102023927267123763170801155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136031903022831684227734873 102023927267123763170801155)
      ·
        refine ⟨153035890900685644756201733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102023927267123763170801155 153035890900685644756201733)
        ·
          refine ⟨28694229543878558391787825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 153035890900685644756201733 28694229543878558391787825)
          ·
            refine ⟨21520672157908918793840869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28694229543878558391787825 21520672157908918793840869)
            ·
              refine ⟨4035126029607922273845163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21520672157908918793840869 4035126029607922273845163)
              ·
                refine ⟨6052689044411883410767745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4035126029607922273845163 6052689044411883410767745)
                ·
                  refine ⟨4539516783308912558075809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6052689044411883410767745 4539516783308912558075809)
                  ·
                    refine ⟨3404637587481684418556857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4539516783308912558075809 3404637587481684418556857)
                    ·
                      refine ⟨2553478190611263313917643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3404637587481684418556857 2553478190611263313917643)
                      ·
                        rfl

theorem cell23_4972881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 4, 1, 2, 2, 2].length) (baseStart_4972881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4972881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4972881 prefixEnd_4972881 := by exact prefixLift 4972881
  have htrace : WordTrace (prefixWord ++ tailWord_4972881) baseStart_4972881 baseEnd_4972881 := by
    simpa [prefixWord, tailWord_4972881, baseEnd_4972881] using wordTrace_append hprefix tailTrace_4972881
  have hstable : (prefixWord ++ tailWord_4972881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4972881).length < 2 ^ (prefixWord ++ tailWord_4972881).sum := by decide
  have hdescent : baseEnd_4972881 < baseStart_4972881 := by decide
  rcases family_descends (prefixWord ++ tailWord_4972881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4972883 : List Nat := [1, 1, 1, 2, 1, 1, 4, 4, 1, 7]
def baseStart_4972883 : Nat := 118140960795 + 4972883 * 2 ^ 59
def prefixEnd_4972883 : Nat := 4983230072969 + 3 ^ 40 * 4972883 * 2
def baseEnd_4972883 : Nat := 851159739190857435364211

theorem tailTrace_4972883 : CollatzResearch.WordTrace tailWord_4972883 prefixEnd_4972883 851159739190857435364211 := by
  unfold tailWord_4972883
  simp only [CollatzResearch.WordTrace]
  refine ⟨181375943643101666645219303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120917295762067777763479535 181375943643101666645219303)
  ·
    refine ⟨272063915464652499967828955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181375943643101666645219303 272063915464652499967828955)
    ·
      refine ⟨408095873196978749951743433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272063915464652499967828955 408095873196978749951743433)
      ·
        refine ⟨306071904897734062463807575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 408095873196978749951743433 306071904897734062463807575)
        ·
          refine ⟨459107857346601093695711363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 306071904897734062463807575 459107857346601093695711363)
          ·
            refine ⟨688661786019901640543567045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 459107857346601093695711363 688661786019901640543567045)
            ·
              refine ⟨129124084878731557601918821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 688661786019901640543567045 129124084878731557601918821)
              ·
                refine ⟨24210765914762167050359779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 129124084878731557601918821 24210765914762167050359779)
                ·
                  refine ⟨36316148872143250575539669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24210765914762167050359779 36316148872143250575539669)
                  ·
                    refine ⟨851159739190857435364211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36316148872143250575539669 851159739190857435364211)
                    ·
                      rfl

theorem cell23_4972883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 7].length) (baseStart_4972883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4972883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4972883 prefixEnd_4972883 := by exact prefixLift 4972883
  have htrace : WordTrace (prefixWord ++ tailWord_4972883) baseStart_4972883 baseEnd_4972883 := by
    simpa [prefixWord, tailWord_4972883, baseEnd_4972883] using wordTrace_append hprefix tailTrace_4972883
  have hstable : (prefixWord ++ tailWord_4972883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4972883).length < 2 ^ (prefixWord ++ tailWord_4972883).sum := by decide
  have hdescent : baseEnd_4972883 < baseStart_4972883 := by decide
  rcases family_descends (prefixWord ++ tailWord_4972883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4972917 : List Nat := [1, 3, 4, 1, 2, 1, 2, 2, 2, 5]
def baseStart_4972917 : Nat := 118140960795 + 4972917 * 2 ^ 59
def prefixEnd_4972917 : Nat := 4983230072969 + 3 ^ 40 * 4972917 * 2
def baseEnd_4972917 : Nat := 851165558638275057689159

theorem tailTrace_4972917 : CollatzResearch.WordTrace tailWord_4972917 prefixEnd_4972917 851165558638275057689159 := by
  unfold tailWord_4972917
  simp only [CollatzResearch.WordTrace]
  refine ⟨181377183724978490451957005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120918122483318993634638003 181377183724978490451957005)
  ·
    refine ⟨68016443896866933919483877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181377183724978490451957005 68016443896866933919483877)
    ·
      refine ⟨12753083230662550109903227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68016443896866933919483877 12753083230662550109903227)
      ·
        refine ⟨19129624845993825164854841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12753083230662550109903227 19129624845993825164854841)
        ·
          refine ⟨14347218634495368873641131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19129624845993825164854841 14347218634495368873641131)
          ·
            refine ⟨21520827951743053310461697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14347218634495368873641131 21520827951743053310461697)
            ·
              refine ⟨16140620963807289982846273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21520827951743053310461697 16140620963807289982846273)
              ·
                refine ⟨12105465722855467487134705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16140620963807289982846273 12105465722855467487134705)
                ·
                  refine ⟨9079099292141600615351029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12105465722855467487134705 9079099292141600615351029)
                  ·
                    refine ⟨851165558638275057689159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9079099292141600615351029 851165558638275057689159)
                    ·
                      rfl

theorem cell23_4972917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_4972917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4972917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4972917 prefixEnd_4972917 := by exact prefixLift 4972917
  have htrace : WordTrace (prefixWord ++ tailWord_4972917) baseStart_4972917 baseEnd_4972917 := by
    simpa [prefixWord, tailWord_4972917, baseEnd_4972917] using wordTrace_append hprefix tailTrace_4972917
  have hstable : (prefixWord ++ tailWord_4972917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4972917).length < 2 ^ (prefixWord ++ tailWord_4972917).sum := by decide
  have hdescent : baseEnd_4972917 < baseStart_4972917 := by decide
  rcases family_descends (prefixWord ++ tailWord_4972917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4972937 : List Nat := [1, 2, 1, 1, 6, 1, 1, 1, 1, 6, 2]
def baseStart_4972937 : Nat := 118140960795 + 4972937 * 2 ^ 59
def prefixEnd_4972937 : Nat := 4983230072969 + 3 ^ 40 * 4972937 * 2
def baseEnd_4972937 : Nat := 2553506945527915094817385

theorem tailTrace_4972937 : CollatzResearch.WordTrace tailWord_4972937 prefixEnd_4972937 2553506945527915094817385 := by
  unfold tailWord_4972937
  simp only [CollatzResearch.WordTrace]
  refine ⟨181377913184906033867685065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120918608789937355911790043 181377913184906033867685065)
  ·
    refine ⟨136033434888679525400763799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181377913184906033867685065 136033434888679525400763799)
    ·
      refine ⟨204050152333019288101145699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136033434888679525400763799 204050152333019288101145699)
      ·
        refine ⟨306075228499528932151718549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204050152333019288101145699 306075228499528932151718549)
        ·
          refine ⟨14347276335915418694611807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 306075228499528932151718549 14347276335915418694611807)
          ·
            refine ⟨21520914503873128041917711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14347276335915418694611807 21520914503873128041917711)
            ·
              refine ⟨32281371755809692062876567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21520914503873128041917711 32281371755809692062876567)
              ·
                refine ⟨48422057633714538094314851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32281371755809692062876567 48422057633714538094314851)
                ·
                  refine ⟨72633086450571807141472277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48422057633714538094314851 72633086450571807141472277)
                  ·
                    refine ⟨3404675927370553459756513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 72633086450571807141472277 3404675927370553459756513)
                    ·
                      refine ⟨2553506945527915094817385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3404675927370553459756513 2553506945527915094817385)
                      ·
                        rfl

theorem cell23_4972937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 6, 2].length) (baseStart_4972937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4972937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4972937 prefixEnd_4972937 := by exact prefixLift 4972937
  have htrace : WordTrace (prefixWord ++ tailWord_4972937) baseStart_4972937 baseEnd_4972937 := by
    simpa [prefixWord, tailWord_4972937, baseEnd_4972937] using wordTrace_append hprefix tailTrace_4972937
  have hstable : (prefixWord ++ tailWord_4972937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4972937).length < 2 ^ (prefixWord ++ tailWord_4972937).sum := by decide
  have hdescent : baseEnd_4972937 < baseStart_4972937 := by decide
  rcases family_descends (prefixWord ++ tailWord_4972937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4972954 : List Nat := [3, 1, 1, 4, 1, 4, 1, 1, 2, 1, 4]
def baseStart_4972954 : Nat := 118140960795 + 4972954 * 2 ^ 59
def prefixEnd_4972954 : Nat := 4983230072969 + 3 ^ 40 * 4972954 * 2
def baseEnd_4972954 : Nat := 2553515674699041528304807

theorem tailTrace_4972954 : CollatzResearch.WordTrace tailWord_4972954 prefixEnd_4972954 2553515674699041528304807 := by
  unfold tailWord_4972954
  simp only [CollatzResearch.WordTrace]
  refine ⟨45344633306461111442763479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120919022150562963847369277 45344633306461111442763479)
  ·
    refine ⟨68016949959691667164145219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45344633306461111442763479 68016949959691667164145219)
    ·
      refine ⟨102025424939537500746217829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68016949959691667164145219 102025424939537500746217829)
      ·
        refine ⟨19129767176163281389915843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102025424939537500746217829 19129767176163281389915843)
        ·
          refine ⟨28694650764244922084873765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19129767176163281389915843 28694650764244922084873765)
          ·
            refine ⟨5380247018295922890913831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28694650764244922084873765 5380247018295922890913831)
            ·
              refine ⟨8070370527443884336370747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5380247018295922890913831 8070370527443884336370747)
              ·
                refine ⟨12105555791165826504556121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8070370527443884336370747 12105555791165826504556121)
                ·
                  refine ⟨9079166843374369878417091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12105555791165826504556121 9079166843374369878417091)
                  ·
                    refine ⟨13618750265061554817625637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9079166843374369878417091 13618750265061554817625637)
                    ·
                      refine ⟨2553515674699041528304807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13618750265061554817625637 2553515674699041528304807)
                      ·
                        rfl

theorem cell23_4972954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_4972954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4972954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4972954 prefixEnd_4972954 := by exact prefixLift 4972954
  have htrace : WordTrace (prefixWord ++ tailWord_4972954) baseStart_4972954 baseEnd_4972954 := by
    simpa [prefixWord, tailWord_4972954, baseEnd_4972954] using wordTrace_append hprefix tailTrace_4972954
  have hstable : (prefixWord ++ tailWord_4972954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4972954).length < 2 ^ (prefixWord ++ tailWord_4972954).sum := by decide
  have hdescent : baseEnd_4972954 < baseStart_4972954 := by decide
  rcases family_descends (prefixWord ++ tailWord_4972954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4972964 : List Nat := [2, 3, 1, 2, 1, 1, 3, 5, 1, 4]
def baseStart_4972964 : Nat := 118140960795 + 4972964 * 2 ^ 59
def prefixEnd_4972964 : Nat := 4983230072969 + 3 ^ 40 * 4972964 * 2
def baseEnd_4972964 : Nat := 851173603168528829726587

theorem tailTrace_4972964 : CollatzResearch.WordTrace tailWord_4972964 prefixEnd_4972964 851173603168528829726587 := by
  unfold tailWord_4972964
  simp only [CollatzResearch.WordTrace]
  refine ⟨90689448977904108739458973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120919265303872144985945297 90689448977904108739458973)
  ·
    refine ⟨34008543366714040777297115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90689448977904108739458973 34008543366714040777297115)
    ·
      refine ⟨51012815050071061165945673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34008543366714040777297115 51012815050071061165945673)
      ·
        refine ⟨38259611287553295874459255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51012815050071061165945673 38259611287553295874459255)
        ·
          refine ⟨57389416931329943811688883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38259611287553295874459255 57389416931329943811688883)
          ·
            refine ⟨86084125396994915717533325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57389416931329943811688883 86084125396994915717533325)
            ·
              refine ⟨32281547023873093394074997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86084125396994915717533325 32281547023873093394074997)
              ·
                refine ⟨3026395033488102505694531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32281547023873093394074997 3026395033488102505694531)
                ·
                  refine ⟨4539592550232153758541797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3026395033488102505694531 4539592550232153758541797)
                  ·
                    refine ⟨851173603168528829726587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4539592550232153758541797 851173603168528829726587)
                    ·
                      rfl

theorem cell23_4972964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 5, 1, 4].length) (baseStart_4972964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4972964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4972964 prefixEnd_4972964 := by exact prefixLift 4972964
  have htrace : WordTrace (prefixWord ++ tailWord_4972964) baseStart_4972964 baseEnd_4972964 := by
    simpa [prefixWord, tailWord_4972964, baseEnd_4972964] using wordTrace_append hprefix tailTrace_4972964
  have hstable : (prefixWord ++ tailWord_4972964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4972964).length < 2 ^ (prefixWord ++ tailWord_4972964).sum := by decide
  have hdescent : baseEnd_4972964 < baseStart_4972964 := by decide
  rcases family_descends (prefixWord ++ tailWord_4972964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4972977 : List Nat := [1, 2, 2, 4, 1, 2, 3, 2, 6]
def baseStart_4972977 : Nat := 118140960795 + 4972977 * 2 ^ 59
def prefixEnd_4972977 : Nat := 4983230072969 + 3 ^ 40 * 4972977 * 2
def baseEnd_4972977 : Nat := 283725276083788326479689

theorem tailTrace_4972977 : CollatzResearch.WordTrace tailWord_4972977 prefixEnd_4972977 283725276083788326479689 := by
  unfold tailWord_4972977
  simp only [CollatzResearch.WordTrace]
  refine ⟨181379372104761120699141185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120919581403174080466094123 181379372104761120699141185)
  ·
    refine ⟨136034529078570840524355889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181379372104761120699141185 136034529078570840524355889)
    ·
      refine ⟨102025896808928130393266917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136034529078570840524355889 102025896808928130393266917)
      ·
        refine ⟨19129855651674024448737547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102025896808928130393266917 19129855651674024448737547)
        ·
          refine ⟨28694783477511036673106321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19129855651674024448737547 28694783477511036673106321)
          ·
            refine ⟨21521087608133277504829741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28694783477511036673106321 21521087608133277504829741)
            ·
              refine ⟨8070407853049979064311153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21521087608133277504829741 8070407853049979064311153)
              ·
                refine ⟨6052805889787484298233365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8070407853049979064311153 6052805889787484298233365)
                ·
                  refine ⟨283725276083788326479689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6052805889787484298233365 283725276083788326479689)
                  ·
                    rfl

theorem cell23_4972977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 2, 6].length) (baseStart_4972977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4972977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4972977 prefixEnd_4972977 := by exact prefixLift 4972977
  have htrace : WordTrace (prefixWord ++ tailWord_4972977) baseStart_4972977 baseEnd_4972977 := by
    simpa [prefixWord, tailWord_4972977, baseEnd_4972977] using wordTrace_append hprefix tailTrace_4972977
  have hstable : (prefixWord ++ tailWord_4972977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4972977).length < 2 ^ (prefixWord ++ tailWord_4972977).sum := by decide
  have hdescent : baseEnd_4972977 < baseStart_4972977 := by decide
  rcases family_descends (prefixWord ++ tailWord_4972977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4973040 : List Nat := [2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 6]
def baseStart_4973040 : Nat := 118140960795 + 4973040 * 2 ^ 59
def prefixEnd_4973040 : Nat := 4983230072969 + 3 ^ 40 * 4973040 * 2
def baseEnd_4973040 : Nat := 2553559834035328191829411

theorem tailTrace_4973040 : CollatzResearch.WordTrace tailWord_4973040 prefixEnd_4973040 2553559834035328191829411 := by
  unfold tailWord_4973040
  simp only [CollatzResearch.WordTrace]
  refine ⟨90690834951766441229342287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120921113269021921639123049 90690834951766441229342287)
  ·
    refine ⟨136036252427649661844013431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90690834951766441229342287 136036252427649661844013431)
    ·
      refine ⟨204054378641474492766020147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136036252427649661844013431 204054378641474492766020147)
      ·
        refine ⟨306081567962211739149030221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204054378641474492766020147 306081567962211739149030221)
        ·
          refine ⟨114780587985829402180886333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 306081567962211739149030221 114780587985829402180886333)
          ·
            refine ⟨43042720494686025817832375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114780587985829402180886333 43042720494686025817832375)
            ·
              refine ⟨64564080742029038726748563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43042720494686025817832375 64564080742029038726748563)
              ·
                refine ⟨96846121113043558090122845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64564080742029038726748563 96846121113043558090122845)
                ·
                  refine ⟨36317295417391334283796067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96846121113043558090122845 36317295417391334283796067)
                  ·
                    refine ⟨54475943126087001425694101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36317295417391334283796067 54475943126087001425694101)
                    ·
                      refine ⟨2553559834035328191829411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54475943126087001425694101 2553559834035328191829411)
                      ·
                        rfl

theorem cell23_4973040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 6].length) (baseStart_4973040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4973040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4973040 prefixEnd_4973040 := by exact prefixLift 4973040
  have htrace : WordTrace (prefixWord ++ tailWord_4973040) baseStart_4973040 baseEnd_4973040 := by
    simpa [prefixWord, tailWord_4973040, baseEnd_4973040] using wordTrace_append hprefix tailTrace_4973040
  have hstable : (prefixWord ++ tailWord_4973040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4973040).length < 2 ^ (prefixWord ++ tailWord_4973040).sum := by decide
  have hdescent : baseEnd_4973040 < baseStart_4973040 := by decide
  rcases family_descends (prefixWord ++ tailWord_4973040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4973057 : List Nat := [1, 2, 4, 1, 3, 1, 2, 1, 1, 1, 6]
def baseStart_4973057 : Nat := 118140960795 + 4973057 * 2 ^ 59
def prefixEnd_4973057 : Nat := 4983230072969 + 3 ^ 40 * 4973057 * 2
def baseEnd_4973057 : Nat := 2553568563206454625316833

theorem tailTrace_4973057 : CollatzResearch.WordTrace tailWord_4973057 prefixEnd_4973057 2553568563206454625316833 := by
  unfold tailWord_4973057
  simp only [CollatzResearch.WordTrace]
  refine ⟨181382289944471294362053425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120921526629647529574702283 181382289944471294362053425)
  ·
    refine ⟨136036717458353470771540069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181382289944471294362053425 136036717458353470771540069)
    ·
      refine ⟨25506884523441275769663763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 136036717458353470771540069 25506884523441275769663763)
      ·
        refine ⟨38260326785161913654495645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25506884523441275769663763 38260326785161913654495645)
        ·
          refine ⟨14347622544435717620435867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38260326785161913654495645 14347622544435717620435867)
          ·
            refine ⟨21521433816653576430653801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14347622544435717620435867 21521433816653576430653801)
            ·
              refine ⟨16141075362490182322990351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21521433816653576430653801 16141075362490182322990351)
              ·
                refine ⟨24211613043735273484485527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16141075362490182322990351 24211613043735273484485527)
                ·
                  refine ⟨36317419565602910226728291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24211613043735273484485527 36317419565602910226728291)
                  ·
                    refine ⟨54476129348404365340092437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36317419565602910226728291 54476129348404365340092437)
                    ·
                      refine ⟨2553568563206454625316833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54476129348404365340092437 2553568563206454625316833)
                      ·
                        rfl

theorem cell23_4973057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_4973057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4973057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4973057 prefixEnd_4973057 := by exact prefixLift 4973057
  have htrace : WordTrace (prefixWord ++ tailWord_4973057) baseStart_4973057 baseEnd_4973057 := by
    simpa [prefixWord, tailWord_4973057, baseEnd_4973057] using wordTrace_append hprefix tailTrace_4973057
  have hstable : (prefixWord ++ tailWord_4973057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4973057).length < 2 ^ (prefixWord ++ tailWord_4973057).sum := by decide
  have hdescent : baseEnd_4973057 < baseStart_4973057 := by decide
  rcases family_descends (prefixWord ++ tailWord_4973057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4973058 : List Nat := [3, 4, 1, 2, 2, 2, 1, 2, 1, 5]
def baseStart_4973058 : Nat := 118140960795 + 4973058 * 2 ^ 59
def prefixEnd_4973058 : Nat := 4983230072969 + 3 ^ 40 * 4973058 * 2
def baseEnd_4973058 : Nat := 851189692229036373801443

theorem tailTrace_4973058 : CollatzResearch.WordTrace tailWord_4973058 prefixEnd_4973058 851189692229036373801443 := by
  unfold tailWord_4973058
  simp only [CollatzResearch.WordTrace]
  refine ⟨45345581604366917883209957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120921550944978447688559885 45345581604366917883209957)
  ·
    refine ⟨8502296550818797103101867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45345581604366917883209957 8502296550818797103101867)
    ·
      refine ⟨12753444826228195654652801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8502296550818797103101867 12753444826228195654652801)
      ·
        refine ⟨9565083619671146740989601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12753444826228195654652801 9565083619671146740989601)
        ·
          refine ⟨7173812714753360055742201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9565083619671146740989601 7173812714753360055742201)
          ·
            refine ⟨5380359536065020041806651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7173812714753360055742201 5380359536065020041806651)
            ·
              refine ⟨8070539304097530062709977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5380359536065020041806651 8070539304097530062709977)
              ·
                refine ⟨6052904478073147547032483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8070539304097530062709977 6052904478073147547032483)
                ·
                  refine ⟨9079356717109721320548725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6052904478073147547032483 9079356717109721320548725)
                  ·
                    refine ⟨851189692229036373801443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9079356717109721320548725 851189692229036373801443)
                    ·
                      rfl

theorem cell23_4973058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_4973058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4973058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4973058 prefixEnd_4973058 := by exact prefixLift 4973058
  have htrace : WordTrace (prefixWord ++ tailWord_4973058) baseStart_4973058 baseEnd_4973058 := by
    simpa [prefixWord, tailWord_4973058, baseEnd_4973058] using wordTrace_append hprefix tailTrace_4973058
  have hstable : (prefixWord ++ tailWord_4973058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4973058).length < 2 ^ (prefixWord ++ tailWord_4973058).sum := by decide
  have hdescent : baseEnd_4973058 < baseStart_4973058 := by decide
  rcases family_descends (prefixWord ++ tailWord_4973058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4973104 : List Nat := [2, 1, 1, 1, 2, 3, 3, 2, 3, 3, 2]
def baseStart_4973104 : Nat := 118140960795 + 4973104 * 2 ^ 59
def prefixEnd_4973104 : Nat := 4983230072969 + 3 ^ 40 * 4973104 * 2
def baseEnd_4973104 : Nat := 2553592696797215941429117

theorem tailTrace_4973104 : CollatzResearch.WordTrace tailWord_4973104 prefixEnd_4973104 2553592696797215941429117 := by
  unfold tailWord_4973104
  simp only [CollatzResearch.WordTrace]
  refine ⟨90692002087650510694507183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120922669450200680926009577 90692002087650510694507183)
  ·
    refine ⟨136038003131475766041760775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90692002087650510694507183 136038003131475766041760775)
    ·
      refine ⟨204057004697213649062641163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136038003131475766041760775 204057004697213649062641163)
      ·
        refine ⟨306085507045820473593961745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204057004697213649062641163 306085507045820473593961745)
        ·
          refine ⟨229564130284365355195471309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 306085507045820473593961745 229564130284365355195471309)
          ·
            refine ⟨86086548856637008198301741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 229564130284365355195471309 86086548856637008198301741)
            ·
              refine ⟨32282455821238878074363153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86086548856637008198301741 32282455821238878074363153)
              ·
                refine ⟨24211841865929158555772365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32282455821238878074363153 24211841865929158555772365)
                ·
                  refine ⟨9079440699723434458414637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24211841865929158555772365 9079440699723434458414637)
                  ·
                    refine ⟨3404790262396287921905489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9079440699723434458414637 3404790262396287921905489)
                    ·
                      refine ⟨2553592696797215941429117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3404790262396287921905489 2553592696797215941429117)
                      ·
                        rfl

theorem cell23_4973104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 3, 3, 2].length) (baseStart_4973104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4973104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4973104 prefixEnd_4973104 := by exact prefixLift 4973104
  have htrace : WordTrace (prefixWord ++ tailWord_4973104) baseStart_4973104 baseEnd_4973104 := by
    simpa [prefixWord, tailWord_4973104, baseEnd_4973104] using wordTrace_append hprefix tailTrace_4973104
  have hstable : (prefixWord ++ tailWord_4973104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4973104).length < 2 ^ (prefixWord ++ tailWord_4973104).sum := by decide
  have hdescent : baseEnd_4973104 < baseStart_4973104 := by decide
  rcases family_descends (prefixWord ++ tailWord_4973104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4973108 : List Nat := [2, 5, 1, 3, 1, 1, 2, 1, 1, 2, 4]
def baseStart_4973108 : Nat := 118140960795 + 4973108 * 2 ^ 59
def prefixEnd_4973108 : Nat := 4983230072969 + 3 ^ 40 * 4973108 * 2
def baseEnd_4973108 : Nat := 2553594750719833925779099

theorem tailTrace_4973108 : CollatzResearch.WordTrace tailWord_4973108 prefixEnd_4973108 2553594750719833925779099 := by
  unfold tailWord_4973108
  simp only [CollatzResearch.WordTrace]
  refine ⟨90692075033643265036079989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120922766711524353381439985 90692075033643265036079989)
  ·
    refine ⟨8502382034404056097132499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 90692075033643265036079989 8502382034404056097132499)
    ·
      refine ⟨12753573051606084145698749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8502382034404056097132499 12753573051606084145698749)
      ·
        refine ⟨4782589894352281554637031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12753573051606084145698749 4782589894352281554637031)
        ·
          refine ⟨7173884841528422331955547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4782589894352281554637031 7173884841528422331955547)
          ·
            refine ⟨10760827262292633497933321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7173884841528422331955547 10760827262292633497933321)
            ·
              refine ⟨8070620446719475123449991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10760827262292633497933321 8070620446719475123449991)
              ·
                refine ⟨12105930670079212685174987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8070620446719475123449991 12105930670079212685174987)
                ·
                  refine ⟨18158896005118819027762481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12105930670079212685174987 18158896005118819027762481)
                  ·
                    refine ⟨13619172003839114270821861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18158896005118819027762481 13619172003839114270821861)
                    ·
                      refine ⟨2553594750719833925779099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13619172003839114270821861 2553594750719833925779099)
                      ·
                        rfl

theorem cell23_4973108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_4973108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4973108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4973108 prefixEnd_4973108 := by exact prefixLift 4973108
  have htrace : WordTrace (prefixWord ++ tailWord_4973108) baseStart_4973108 baseEnd_4973108 := by
    simpa [prefixWord, tailWord_4973108, baseEnd_4973108] using wordTrace_append hprefix tailTrace_4973108
  have hstable : (prefixWord ++ tailWord_4973108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4973108).length < 2 ^ (prefixWord ++ tailWord_4973108).sum := by decide
  have hdescent : baseEnd_4973108 < baseStart_4973108 := by decide
  rcases family_descends (prefixWord ++ tailWord_4973108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4973121 : List Nat := [1, 2, 5, 1, 1, 2, 2, 1, 3, 3, 2]
def baseStart_4973121 : Nat := 118140960795 + 4973121 * 2 ^ 59
def prefixEnd_4973121 : Nat := 4983230072969 + 3 ^ 40 * 4973121 * 2
def baseEnd_4973121 : Nat := 2553601425968342374916539

theorem tailTrace_4973121 : CollatzResearch.WordTrace tailWord_4973121 prefixEnd_4973121 2553601425968342374916539 := by
  unfold tailWord_4973121
  simp only [CollatzResearch.WordTrace]
  refine ⟨181384624216239433292383217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120923082810826288861588811 181384624216239433292383217)
  ·
    refine ⟨136038468162179574969287413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181384624216239433292383217 136038468162179574969287413)
    ·
      refine ⟨12753606390204335153370695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 136038468162179574969287413 12753606390204335153370695)
      ·
        refine ⟨19130409585306502730056043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12753606390204335153370695 19130409585306502730056043)
        ·
          refine ⟨28695614377959754095084065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19130409585306502730056043 28695614377959754095084065)
          ·
            refine ⟨21521710783469815571313049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28695614377959754095084065 21521710783469815571313049)
            ·
              refine ⟨16141283087602361678484787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21521710783469815571313049 16141283087602361678484787)
              ·
                refine ⟨24211924631403542517727181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16141283087602361678484787 24211924631403542517727181)
                ·
                  refine ⟨9079471736776328444147693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24211924631403542517727181 9079471736776328444147693)
                  ·
                    refine ⟨3404801901291123166555385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9079471736776328444147693 3404801901291123166555385)
                    ·
                      refine ⟨2553601425968342374916539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3404801901291123166555385 2553601425968342374916539)
                      ·
                        rfl

theorem cell23_4973121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 3, 3, 2].length) (baseStart_4973121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4973121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4973121 prefixEnd_4973121 := by exact prefixLift 4973121
  have htrace : WordTrace (prefixWord ++ tailWord_4973121) baseStart_4973121 baseEnd_4973121 := by
    simpa [prefixWord, tailWord_4973121, baseEnd_4973121] using wordTrace_append hprefix tailTrace_4973121
  have hstable : (prefixWord ++ tailWord_4973121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4973121).length < 2 ^ (prefixWord ++ tailWord_4973121).sum := by decide
  have hdescent : baseEnd_4973121 < baseStart_4973121 := by decide
  rcases family_descends (prefixWord ++ tailWord_4973121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4973168 : List Nat := [2, 1, 1, 1, 7, 2, 1, 1, 1, 4, 2]
def baseStart_4973168 : Nat := 118140960795 + 4973168 * 2 ^ 59
def prefixEnd_4973168 : Nat := 4983230072969 + 3 ^ 40 * 4973168 * 2
def baseEnd_4973168 : Nat := 2553625559559103691028823

theorem tailTrace_4973168 : CollatzResearch.WordTrace tailWord_4973168 prefixEnd_4973168 2553625559559103691028823 := by
  unfold tailWord_4973168
  simp only [CollatzResearch.WordTrace]
  refine ⟨90693169223534580159672079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120924225631379440212896105 90693169223534580159672079)
  ·
    refine ⟨136039753835301870239508119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90693169223534580159672079 136039753835301870239508119)
    ·
      refine ⟨204059630752952805359262179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136039753835301870239508119 204059630752952805359262179)
      ·
        refine ⟨306089446129429208038893269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204059630752952805359262179 306089446129429208038893269)
        ·
          refine ⟨7173971393658497063411561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 306089446129429208038893269 7173971393658497063411561)
          ·
            refine ⟨5380478545243872797558671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7173971393658497063411561 5380478545243872797558671)
            ·
              refine ⟨8070717817865809196338007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5380478545243872797558671 8070717817865809196338007)
              ·
                refine ⟨12106076726798713794507011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8070717817865809196338007 12106076726798713794507011)
                ·
                  refine ⟨18159115090198070691760517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12106076726798713794507011 18159115090198070691760517)
                  ·
                    refine ⟨3404834079412138254705097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18159115090198070691760517 3404834079412138254705097)
                    ·
                      refine ⟨2553625559559103691028823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3404834079412138254705097 2553625559559103691028823)
                      ·
                        rfl

theorem cell23_4973168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 1, 1, 4, 2].length) (baseStart_4973168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4973168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4973168 prefixEnd_4973168 := by exact prefixLift 4973168
  have htrace : WordTrace (prefixWord ++ tailWord_4973168) baseStart_4973168 baseEnd_4973168 := by
    simpa [prefixWord, tailWord_4973168, baseEnd_4973168] using wordTrace_append hprefix tailTrace_4973168
  have hstable : (prefixWord ++ tailWord_4973168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4973168).length < 2 ^ (prefixWord ++ tailWord_4973168).sum := by decide
  have hdescent : baseEnd_4973168 < baseStart_4973168 := by decide
  rcases family_descends (prefixWord ++ tailWord_4973168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4973187 : List Nat := [1, 1, 1, 3, 3, 1, 4, 1, 1, 7]
def baseStart_4973187 : Nat := 118140960795 + 4973187 * 2 ^ 59
def prefixEnd_4973187 : Nat := 4983230072969 + 3 ^ 40 * 4973187 * 2
def baseEnd_4973187 : Nat := 851211771897179705563745

theorem tailTrace_4973187 : CollatzResearch.WordTrace tailWord_4973187 prefixEnd_4973187 851211771897179705563745 := by
  unfold tailWord_4973187
  simp only [CollatzResearch.WordTrace]
  refine ⟨181387031434000326564285815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120924687622666884376190543 181387031434000326564285815)
  ·
    refine ⟨272080547151000489846428723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181387031434000326564285815 272080547151000489846428723)
    ·
      refine ⟨408120820726500734769643085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272080547151000489846428723 408120820726500734769643085)
      ·
        refine ⟨153045307772437775538616157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 408120820726500734769643085 153045307772437775538616157)
        ·
          refine ⟨57391990414664165826981059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 153045307772437775538616157 57391990414664165826981059)
          ·
            refine ⟨86087985621996248740471589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57391990414664165826981059 86087985621996248740471589)
            ·
              refine ⟨16141497304124296638838423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86087985621996248740471589 16141497304124296638838423)
              ·
                refine ⟨24212245956186444958257635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16141497304124296638838423 24212245956186444958257635)
                ·
                  refine ⟨36318368934279667437386453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24212245956186444958257635 36318368934279667437386453)
                  ·
                    refine ⟨851211771897179705563745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36318368934279667437386453 851211771897179705563745)
                    ·
                      rfl

theorem cell23_4973187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 7].length) (baseStart_4973187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4973187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4973187 prefixEnd_4973187 := by exact prefixLift 4973187
  have htrace : WordTrace (prefixWord ++ tailWord_4973187) baseStart_4973187 baseEnd_4973187 := by
    simpa [prefixWord, tailWord_4973187, baseEnd_4973187] using wordTrace_append hprefix tailTrace_4973187
  have hstable : (prefixWord ++ tailWord_4973187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4973187).length < 2 ^ (prefixWord ++ tailWord_4973187).sum := by decide
  have hdescent : baseEnd_4973187 < baseStart_4973187 := by decide
  rcases family_descends (prefixWord ++ tailWord_4973187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4973234 : List Nat := [3, 2, 1, 1, 1, 2, 1, 3, 5, 4]
def baseStart_4973234 : Nat := 118140960795 + 4973234 * 2 ^ 59
def prefixEnd_4973234 : Nat := 4983230072969 + 3 ^ 40 * 4973234 * 2
def baseEnd_4973234 : Nat := 851219816427433477601173

theorem tailTrace_4973234 : CollatzResearch.WordTrace tailWord_4973234 prefixEnd_4973234 851219816427433477601173 := by
  unfold tailWord_4973234
  simp only [CollatzResearch.WordTrace]
  refine ⟨45347186416207513397811689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120925830443220035727497837 45347186416207513397811689)
  ·
    refine ⟨34010389812155635048358767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45347186416207513397811689 34010389812155635048358767)
    ·
      refine ⟨51015584718233452572538151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34010389812155635048358767 51015584718233452572538151)
      ·
        refine ⟨76523377077350178858807227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51015584718233452572538151 76523377077350178858807227)
        ·
          refine ⟨114785065616025268288210841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76523377077350178858807227 114785065616025268288210841)
          ·
            refine ⟨86088799212018951216158131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114785065616025268288210841 86088799212018951216158131)
            ·
              refine ⟨129133198818028426824237197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86088799212018951216158131 129133198818028426824237197)
              ·
                refine ⟨48424949556760660059088949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 129133198818028426824237197 48424949556760660059088949)
                ·
                  refine ⟨4539839020946311880539589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48424949556760660059088949 4539839020946311880539589)
                  ·
                    refine ⟨851219816427433477601173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4539839020946311880539589 851219816427433477601173)
                    ·
                      rfl

theorem cell23_4973234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 5, 4].length) (baseStart_4973234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4973234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4973234 prefixEnd_4973234 := by exact prefixLift 4973234
  have htrace : WordTrace (prefixWord ++ tailWord_4973234) baseStart_4973234 baseEnd_4973234 := by
    simpa [prefixWord, tailWord_4973234, baseEnd_4973234] using wordTrace_append hprefix tailTrace_4973234
  have hstable : (prefixWord ++ tailWord_4973234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4973234).length < 2 ^ (prefixWord ++ tailWord_4973234).sum := by decide
  have hdescent : baseEnd_4973234 < baseStart_4973234 := by decide
  rcases family_descends (prefixWord ++ tailWord_4973234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4973307 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 2, 10]
def baseStart_4973307 : Nat := 118140960795 + 4973307 * 2 ^ 59
def prefixEnd_4973307 : Nat := 4983230072969 + 3 ^ 40 * 4973307 * 2
def baseEnd_4973307 : Nat := 851232311123359549063561

theorem tailTrace_4973307 : CollatzResearch.WordTrace tailWord_4973307 prefixEnd_4973307 851232311123359549063561 := by
  unfold tailWord_4973307
  simp only [CollatzResearch.WordTrace]
  refine ⟨181391408193565587058654175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120927605462377058039102783 181391408193565587058654175)
  ·
    refine ⟨272087112290348380587981263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181391408193565587058654175 272087112290348380587981263)
    ·
      refine ⟨408130668435522570881971895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272087112290348380587981263 408130668435522570881971895)
      ·
        refine ⟨612196002653283856322957843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 408130668435522570881971895 612196002653283856322957843)
        ·
          refine ⟨918294003979925784484436765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 612196002653283856322957843 918294003979925784484436765)
          ·
            refine ⟨344360251492472169181663787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 918294003979925784484436765 344360251492472169181663787)
            ·
              refine ⟨516540377238708253772495681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 344360251492472169181663787 516540377238708253772495681)
              ·
                refine ⟨387405282929031190329371761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 516540377238708253772495681 387405282929031190329371761)
                ·
                  refine ⟨290553962196773392747028821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 387405282929031190329371761 290553962196773392747028821)
                  ·
                    refine ⟨851232311123359549063561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 290553962196773392747028821 851232311123359549063561)
                    ·
                      rfl

theorem cell23_4973307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 10].length) (baseStart_4973307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4973307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4973307 prefixEnd_4973307 := by exact prefixLift 4973307
  have htrace : WordTrace (prefixWord ++ tailWord_4973307) baseStart_4973307 baseEnd_4973307 := by
    simpa [prefixWord, tailWord_4973307, baseEnd_4973307] using wordTrace_append hprefix tailTrace_4973307
  have hstable : (prefixWord ++ tailWord_4973307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4973307).length < 2 ^ (prefixWord ++ tailWord_4973307).sum := by decide
  have hdescent : baseEnd_4973307 < baseStart_4973307 := by decide
  rcases family_descends (prefixWord ++ tailWord_4973307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4973358 : List Nat := [4, 1, 3, 2, 1, 1, 1, 2, 4, 4]
def baseStart_4973358 : Nat := 118140960795 + 4973358 * 2 ^ 59
def prefixEnd_4973358 : Nat := 4983230072969 + 3 ^ 40 * 4973358 * 2
def baseEnd_4973358 : Nat := 851241040294485982550983

theorem tailTrace_4973358 : CollatzResearch.WordTrace tailWord_4973358 prefixEnd_4973358 851241040294485982550983 := by
  unfold tailWord_4973358
  simp only [CollatzResearch.WordTrace]
  refine ⟨22674158539547602846095091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120928845544253881845840485 22674158539547602846095091)
  ·
    refine ⟨34011237809321404269142637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22674158539547602846095091 34011237809321404269142637)
    ·
      refine ⟨12754214178495526600928489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34011237809321404269142637 12754214178495526600928489)
      ·
        refine ⟨9565660633871644950696367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12754214178495526600928489 9565660633871644950696367)
        ·
          refine ⟨14348490950807467426044551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9565660633871644950696367 14348490950807467426044551)
          ·
            refine ⟨21522736426211201139066827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14348490950807467426044551 21522736426211201139066827)
            ·
              refine ⟨32284104639316801708600241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21522736426211201139066827 32284104639316801708600241)
              ·
                refine ⟨24213078479487601281450181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32284104639316801708600241 24213078479487601281450181)
                ·
                  refine ⟨4539952214903925240271909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24213078479487601281450181 4539952214903925240271909)
                  ·
                    refine ⟨851241040294485982550983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4539952214903925240271909 851241040294485982550983)
                    ·
                      rfl

theorem cell23_4973358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_4973358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4973358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4973358 prefixEnd_4973358 := by exact prefixLift 4973358
  have htrace : WordTrace (prefixWord ++ tailWord_4973358) baseStart_4973358 baseEnd_4973358 := by
    simpa [prefixWord, tailWord_4973358, baseEnd_4973358] using wordTrace_append hprefix tailTrace_4973358
  have hstable : (prefixWord ++ tailWord_4973358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4973358).length < 2 ^ (prefixWord ++ tailWord_4973358).sum := by decide
  have hdescent : baseEnd_4973358 < baseStart_4973358 := by decide
  rcases family_descends (prefixWord ++ tailWord_4973358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4973384 : List Nat := [2, 1, 3, 1, 1, 3, 2, 1, 2, 7]
def baseStart_4973384 : Nat := 118140960795 + 4973384 * 2 ^ 59
def prefixEnd_4973384 : Nat := 4983230072969 + 3 ^ 40 * 4973384 * 2
def baseEnd_4973384 : Nat := 851245490460158281975943

theorem tailTrace_4973384 : CollatzResearch.WordTrace tailWord_4973384 prefixEnd_4973384 851245490460158281975943 := by
  unfold tailWord_4973384
  simp only [CollatzResearch.WordTrace]
  refine ⟨90697108307143314604603603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120929477742857752806138137 90697108307143314604603603)
  ·
    refine ⟨136045662460714971906905405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90697108307143314604603603 136045662460714971906905405)
    ·
      refine ⟨51017123422768114465089527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136045662460714971906905405 51017123422768114465089527)
      ·
        refine ⟨76525685134152171697634291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51017123422768114465089527 76525685134152171697634291)
        ·
          refine ⟨114788527701228257546451437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76525685134152171697634291 114788527701228257546451437)
          ·
            refine ⟨43045697887960596579919289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114788527701228257546451437 43045697887960596579919289)
            ·
              refine ⟨32284273415970447434939467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43045697887960596579919289 32284273415970447434939467)
              ·
                refine ⟨48426410123955671152409201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32284273415970447434939467 48426410123955671152409201)
                ·
                  refine ⟨36319807592966753364306901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48426410123955671152409201 36319807592966753364306901)
                  ·
                    refine ⟨851245490460158281975943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36319807592966753364306901 851245490460158281975943)
                    ·
                      rfl

theorem cell23_4973384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 2, 7].length) (baseStart_4973384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4973384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4973384 prefixEnd_4973384 := by exact prefixLift 4973384
  have htrace : WordTrace (prefixWord ++ tailWord_4973384) baseStart_4973384 baseEnd_4973384 := by
    simpa [prefixWord, tailWord_4973384, baseEnd_4973384] using wordTrace_append hprefix tailTrace_4973384
  have hstable : (prefixWord ++ tailWord_4973384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4973384).length < 2 ^ (prefixWord ++ tailWord_4973384).sum := by decide
  have hdescent : baseEnd_4973384 < baseStart_4973384 := by decide
  rcases family_descends (prefixWord ++ tailWord_4973384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4973408 : List Nat := [2, 1, 1, 3, 3, 1, 3, 1, 3, 3, 2]
def baseStart_4973408 : Nat := 118140960795 + 4973408 * 2 ^ 59
def prefixEnd_4973408 : Nat := 4983230072969 + 3 ^ 40 * 4973408 * 2
def baseEnd_4973408 : Nat := 2553748794916182752027719

theorem tailTrace_4973408 : CollatzResearch.WordTrace tailWord_4973408 prefixEnd_4973408 2553748794916182752027719 := by
  unfold tailWord_4973408
  simp only [CollatzResearch.WordTrace]
  refine ⟨90697545983099840654040439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120930061310799787538720585 90697545983099840654040439)
  ·
    refine ⟨136046318974649760981060659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90697545983099840654040439 136046318974649760981060659)
    ·
      refine ⟨204069478461974641471590989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136046318974649760981060659 204069478461974641471590989)
      ·
        refine ⟨76526054423240490551846621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 204069478461974641471590989 76526054423240490551846621)
        ·
          refine ⟨28697270408715183956942483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76526054423240490551846621 28697270408715183956942483)
          ·
            refine ⟨43045905613072775935413725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28697270408715183956942483 43045905613072775935413725)
            ·
              refine ⟨16142214604902290975780147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43045905613072775935413725 16142214604902290975780147)
              ·
                refine ⟨24213321907353436463670221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16142214604902290975780147 24213321907353436463670221)
                ·
                  refine ⟨9079995715257538673876333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24213321907353436463670221 9079995715257538673876333)
                  ·
                    refine ⟨3404998393221577002703625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9079995715257538673876333 3404998393221577002703625)
                    ·
                      refine ⟨2553748794916182752027719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3404998393221577002703625 2553748794916182752027719)
                      ·
                        rfl

theorem cell23_4973408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 3, 3, 2].length) (baseStart_4973408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4973408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4973408 prefixEnd_4973408 := by exact prefixLift 4973408
  have htrace : WordTrace (prefixWord ++ tailWord_4973408) baseStart_4973408 baseEnd_4973408 := by
    simpa [prefixWord, tailWord_4973408, baseEnd_4973408] using wordTrace_append hprefix tailTrace_4973408
  have hstable : (prefixWord ++ tailWord_4973408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4973408).length < 2 ^ (prefixWord ++ tailWord_4973408).sum := by decide
  have hdescent : baseEnd_4973408 < baseStart_4973408 := by decide
  rcases family_descends (prefixWord ++ tailWord_4973408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4973434 : List Nat := [3, 1, 1, 1, 1, 1, 3, 1, 2, 3, 6]
def baseStart_4973434 : Nat := 118140960795 + 4973434 * 2 ^ 59
def prefixEnd_4973434 : Nat := 4983230072969 + 3 ^ 40 * 4973434 * 2
def baseEnd_4973434 : Nat := 2553762145413199650302599

theorem tailTrace_4973434 : CollatzResearch.WordTrace tailWord_4973434 prefixEnd_4973434 2553762145413199650302599 := by
  unfold tailWord_4973434
  simp only [CollatzResearch.WordTrace]
  refine ⟨45349010066026371937131839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120930693509403658499018237 45349010066026371937131839)
  ·
    refine ⟨68023515099039557905697759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45349010066026371937131839 68023515099039557905697759)
    ·
      refine ⟨102035272648559336858546639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68023515099039557905697759 102035272648559336858546639)
      ·
        refine ⟨153052908972839005287819959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102035272648559336858546639 153052908972839005287819959)
        ·
          refine ⟨229579363459258507931729939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153052908972839005287819959 229579363459258507931729939)
          ·
            refine ⟨344369045188887761897594909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229579363459258507931729939 344369045188887761897594909)
            ·
              refine ⟨129138391945832910711598091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 344369045188887761897594909 129138391945832910711598091)
              ·
                refine ⟨193707587918749366067397137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129138391945832910711598091 193707587918749366067397137)
                ·
                  refine ⟨145280690939062024550547853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 193707587918749366067397137 145280690939062024550547853)
                  ·
                    refine ⟨54480259102148259206455445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 145280690939062024550547853 54480259102148259206455445)
                    ·
                      refine ⟨2553762145413199650302599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54480259102148259206455445 2553762145413199650302599)
                      ·
                        rfl

theorem cell23_4973434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 2, 3, 6].length) (baseStart_4973434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4973434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4973434 prefixEnd_4973434 := by exact prefixLift 4973434
  have htrace : WordTrace (prefixWord ++ tailWord_4973434) baseStart_4973434 baseEnd_4973434 := by
    simpa [prefixWord, tailWord_4973434, baseEnd_4973434] using wordTrace_append hprefix tailTrace_4973434
  have hstable : (prefixWord ++ tailWord_4973434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4973434).length < 2 ^ (prefixWord ++ tailWord_4973434).sum := by decide
  have hdescent : baseEnd_4973434 < baseStart_4973434 := by decide
  rcases family_descends (prefixWord ++ tailWord_4973434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4973461 : List Nat := [1, 3, 2, 1, 1, 5, 1, 2, 7]
def baseStart_4973461 : Nat := 118140960795 + 4973461 * 2 ^ 59
def prefixEnd_4973461 : Nat := 4983230072969 + 3 ^ 40 * 4973461 * 2
def baseEnd_4973461 : Nat := 283752889932319004962775

theorem tailTrace_4973461 : CollatzResearch.WordTrace tailWord_4973461 prefixEnd_4973461 283752889932319004962775 := by
  unfold tailWord_4973461
  simp only [CollatzResearch.WordTrace]
  refine ⟨181397025035007671359760237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120931350023338447573173491 181397025035007671359760237)
  ·
    refine ⟨68023884388127876759910089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181397025035007671359760237 68023884388127876759910089)
    ·
      refine ⟨51017913291095907569932567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68023884388127876759910089 51017913291095907569932567)
      ·
        refine ⟨76526869936643861354898851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51017913291095907569932567 76526869936643861354898851)
        ·
          refine ⟨114790304904965792032348277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76526869936643861354898851 114790304904965792032348277)
          ·
            refine ⟨10761591084840543003032651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 114790304904965792032348277 10761591084840543003032651)
            ·
              refine ⟨16142386627260814504548977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10761591084840543003032651 16142386627260814504548977)
              ·
                refine ⟨12106789970445610878411733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16142386627260814504548977 12106789970445610878411733)
                ·
                  refine ⟨283752889932319004962775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12106789970445610878411733 283752889932319004962775)
                  ·
                    rfl

theorem cell23_4973461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 2, 7].length) (baseStart_4973461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4973461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4973461 prefixEnd_4973461 := by exact prefixLift 4973461
  have htrace : WordTrace (prefixWord ++ tailWord_4973461) baseStart_4973461 baseEnd_4973461 := by
    simpa [prefixWord, tailWord_4973461, baseEnd_4973461] using wordTrace_append hprefix tailTrace_4973461
  have hstable : (prefixWord ++ tailWord_4973461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4973461).length < 2 ^ (prefixWord ++ tailWord_4973461).sum := by decide
  have hdescent : baseEnd_4973461 < baseStart_4973461 := by decide
  rcases family_descends (prefixWord ++ tailWord_4973461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4973489 : List Nat := [1, 2, 2, 4, 3, 2, 1, 2, 2, 2, 2]
def baseStart_4973489 : Nat := 118140960795 + 4973489 * 2 ^ 59
def prefixEnd_4973489 : Nat := 4983230072969 + 3 ^ 40 * 4973489 * 2
def baseEnd_4973489 : Nat := 2553790386849196935114847

theorem tailTrace_4973489 : CollatzResearch.WordTrace tailWord_4973489 prefixEnd_4973489 2553790386849196935114847 := by
  unfold tailWord_4973489
  simp only [CollatzResearch.WordTrace]
  refine ⟨181398046278906232141779521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120932030852604154761186347 181398046278906232141779521)
  ·
    refine ⟨136048534709179674106334641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181398046278906232141779521 136048534709179674106334641)
    ·
      refine ⟨102036401031884755579750981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136048534709179674106334641 102036401031884755579750981)
      ·
        refine ⟨19131825193478391671203309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102036401031884755579750981 19131825193478391671203309)
        ·
          refine ⟨7174434447554396876701241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19131825193478391671203309 7174434447554396876701241)
          ·
            refine ⟨5380825835665797657525931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7174434447554396876701241 5380825835665797657525931)
            ·
              refine ⟨8071238753498696486288897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5380825835665797657525931 8071238753498696486288897)
              ·
                refine ⟨6053429065124022364716673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8071238753498696486288897 6053429065124022364716673)
                ·
                  refine ⟨4540071798843016773537505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6053429065124022364716673 4540071798843016773537505)
                  ·
                    refine ⟨3405053849132262580153129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4540071798843016773537505 3405053849132262580153129)
                    ·
                      refine ⟨2553790386849196935114847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3405053849132262580153129 2553790386849196935114847)
                      ·
                        rfl

theorem cell23_4973489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 2, 2, 2, 2].length) (baseStart_4973489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4973489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4973489 prefixEnd_4973489 := by exact prefixLift 4973489
  have htrace : WordTrace (prefixWord ++ tailWord_4973489) baseStart_4973489 baseEnd_4973489 := by
    simpa [prefixWord, tailWord_4973489, baseEnd_4973489] using wordTrace_append hprefix tailTrace_4973489
  have hstable : (prefixWord ++ tailWord_4973489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4973489).length < 2 ^ (prefixWord ++ tailWord_4973489).sum := by decide
  have hdescent : baseEnd_4973489 < baseStart_4973489 := by decide
  rcases family_descends (prefixWord ++ tailWord_4973489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4973511 : List Nat := [1, 1, 4, 1, 1, 2, 3, 2, 1, 3, 4]
def baseStart_4973511 : Nat := 118140960795 + 4973511 * 2 ^ 59
def prefixEnd_4973511 : Nat := 4983230072969 + 3 ^ 40 * 4973511 * 2
def baseEnd_4973511 : Nat := 2553801683423595849039745

theorem tailTrace_4973511 : CollatzResearch.WordTrace tailWord_4973511 prefixEnd_4973511 2553801683423595849039745 := by
  unfold tailWord_4973511
  simp only [CollatzResearch.WordTrace]
  refine ⟨181398848684826529899080387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120932565789884353266053591 181398848684826529899080387)
  ·
    refine ⟨272098273027239794848620581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181398848684826529899080387 272098273027239794848620581)
    ·
      refine ⟨51018426192607461534116359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 272098273027239794848620581 51018426192607461534116359)
      ·
        refine ⟨76527639288911192301174539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51018426192607461534116359 76527639288911192301174539)
        ·
          refine ⟨114791458933366788451761809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76527639288911192301174539 114791458933366788451761809)
          ·
            refine ⟨86093594200025091338821357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114791458933366788451761809 86093594200025091338821357)
            ·
              refine ⟨32285097825009409252058009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86093594200025091338821357 32285097825009409252058009)
              ·
                refine ⟨24213823368757056939043507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32285097825009409252058009 24213823368757056939043507)
                ·
                  refine ⟨36320735053135585408565261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24213823368757056939043507 36320735053135585408565261)
                  ·
                    refine ⟨13620275644925844528211973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36320735053135585408565261 13620275644925844528211973)
                    ·
                      refine ⟨2553801683423595849039745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13620275644925844528211973 2553801683423595849039745)
                      ·
                        rfl

theorem cell23_4973511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 3, 4].length) (baseStart_4973511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4973511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4973511 prefixEnd_4973511 := by exact prefixLift 4973511
  have htrace : WordTrace (prefixWord ++ tailWord_4973511) baseStart_4973511 baseEnd_4973511 := by
    simpa [prefixWord, tailWord_4973511, baseEnd_4973511] using wordTrace_append hprefix tailTrace_4973511
  have hstable : (prefixWord ++ tailWord_4973511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4973511).length < 2 ^ (prefixWord ++ tailWord_4973511).sum := by decide
  have hdescent : baseEnd_4973511 < baseStart_4973511 := by decide
  rcases family_descends (prefixWord ++ tailWord_4973511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4973551 : List Nat := [1, 1, 2, 1, 4, 3, 2, 1, 8]
def baseStart_4973551 : Nat := 118140960795 + 4973551 * 2 ^ 59
def prefixEnd_4973551 : Nat := 4983230072969 + 3 ^ 40 * 4973551 * 2
def baseEnd_4973551 : Nat := 283758024738863965837729

theorem tailTrace_4973551 : CollatzResearch.WordTrace tailWord_4973551 prefixEnd_4973551 283758024738863965837729 := by
  unfold tailWord_4973551
  simp only [CollatzResearch.WordTrace]
  refine ⟨181400307604681616730536507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120933538403121077820357671 181400307604681616730536507)
  ·
    refine ⟨272100461407022425095804761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181400307604681616730536507 272100461407022425095804761)
    ·
      refine ⟨204075346055266818821853571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 272100461407022425095804761 204075346055266818821853571)
      ·
        refine ⟨306113019082900228232780357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204075346055266818821853571 306113019082900228232780357)
        ·
          refine ⟨57396191078043792793646317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 306113019082900228232780357 57396191078043792793646317)
          ·
            refine ⟨21523571654266422297617369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57396191078043792793646317 21523571654266422297617369)
            ·
              refine ⟨16142678740699816723213027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21523571654266422297617369 16142678740699816723213027)
              ·
                refine ⟨24214018111049725084819541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16142678740699816723213027 24214018111049725084819541)
                ·
                  refine ⟨283758024738863965837729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24214018111049725084819541 283758024738863965837729)
                  ·
                    rfl

theorem cell23_4973551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 8].length) (baseStart_4973551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4973551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4973551 prefixEnd_4973551 := by exact prefixLift 4973551
  have htrace : WordTrace (prefixWord ++ tailWord_4973551) baseStart_4973551 baseEnd_4973551 := by
    simpa [prefixWord, tailWord_4973551, baseEnd_4973551] using wordTrace_append hprefix tailTrace_4973551
  have hstable : (prefixWord ++ tailWord_4973551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4973551).length < 2 ^ (prefixWord ++ tailWord_4973551).sum := by decide
  have hdescent : baseEnd_4973551 < baseStart_4973551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4973551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4973605 : List Nat := [1, 3, 1, 2, 2, 2, 1, 4, 2, 3, 2]
def baseStart_4973605 : Nat := 118140960795 + 4973605 * 2 ^ 59
def prefixEnd_4973605 : Nat := 4983230072969 + 3 ^ 40 * 4973605 * 2
def baseEnd_4973605 : Nat := 2553849950605118481264313

theorem tailTrace_4973605 : CollatzResearch.WordTrace tailWord_4973605 prefixEnd_4973605 2553849950605118481264313 := by
  unfold tailWord_4973605
  simp only [CollatzResearch.WordTrace]
  refine ⟨181402277146485983953002269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120934851430990655968668179 181402277146485983953002269)
  ·
    refine ⟨68025853929932243982375851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181402277146485983953002269 68025853929932243982375851)
    ·
      refine ⟨102038780894898365973563777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68025853929932243982375851 102038780894898365973563777)
      ·
        refine ⟨76529085671173774480172833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102038780894898365973563777 76529085671173774480172833)
        ·
          refine ⟨57396814253380330860129625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76529085671173774480172833 57396814253380330860129625)
          ·
            refine ⟨43047610690035248145097219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57396814253380330860129625 43047610690035248145097219)
            ·
              refine ⟨64571416035052872217645829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43047610690035248145097219 64571416035052872217645829)
              ·
                refine ⟨12107140506572413540808593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64571416035052872217645829 12107140506572413540808593)
                ·
                  refine ⟨9080355379929310155606445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12107140506572413540808593 9080355379929310155606445)
                  ·
                    refine ⟨3405133267473491308352417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9080355379929310155606445 3405133267473491308352417)
                    ·
                      refine ⟨2553849950605118481264313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3405133267473491308352417 2553849950605118481264313)
                      ·
                        rfl

theorem cell23_4973605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 4, 2, 3, 2].length) (baseStart_4973605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4973605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4973605 prefixEnd_4973605 := by exact prefixLift 4973605
  have htrace : WordTrace (prefixWord ++ tailWord_4973605) baseStart_4973605 baseEnd_4973605 := by
    simpa [prefixWord, tailWord_4973605, baseEnd_4973605] using wordTrace_append hprefix tailTrace_4973605
  have hstable : (prefixWord ++ tailWord_4973605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4973605).length < 2 ^ (prefixWord ++ tailWord_4973605).sum := by decide
  have hdescent : baseEnd_4973605 < baseStart_4973605 := by decide
  rcases family_descends (prefixWord ++ tailWord_4973605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4973611 : List Nat := [1, 1, 1, 1, 2, 1, 5, 2, 3, 6]
def baseStart_4973611 : Nat := 118140960795 + 4973611 * 2 ^ 59
def prefixEnd_4973611 : Nat := 4983230072969 + 3 ^ 40 * 4973611 * 2
def baseEnd_4973611 : Nat := 851284343829681819263095

theorem tailTrace_4973611 : CollatzResearch.WordTrace tailWord_4973611 prefixEnd_4973611 851284343829681819263095 := by
  unfold tailWord_4973611
  simp only [CollatzResearch.WordTrace]
  refine ⟨181402495984464246977720687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120934997322976164651813791 181402495984464246977720687)
  ·
    refine ⟨272103743976696370466581031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181402495984464246977720687 272103743976696370466581031)
    ·
      refine ⟨408155615965044555699871547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272103743976696370466581031 408155615965044555699871547)
      ·
        refine ⟨612233423947566833549807321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 408155615965044555699871547 612233423947566833549807321)
        ·
          refine ⟨459175067960675125162355491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 612233423947566833549807321 459175067960675125162355491)
          ·
            refine ⟨688762601941012687743533237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 459175067960675125162355491 688762601941012687743533237)
            ·
              refine ⟨64571493931969939475956241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 688762601941012687743533237 64571493931969939475956241)
              ·
                refine ⟨48428620448977454606967181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64571493931969939475956241 48428620448977454606967181)
                ·
                  refine ⟨18160732668366545477612693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48428620448977454606967181 18160732668366545477612693)
                  ·
                    refine ⟨851284343829681819263095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18160732668366545477612693 851284343829681819263095)
                    ·
                      rfl

theorem cell23_4973611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 3, 6].length) (baseStart_4973611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4973611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4973611 prefixEnd_4973611 := by exact prefixLift 4973611
  have htrace : WordTrace (prefixWord ++ tailWord_4973611) baseStart_4973611 baseEnd_4973611 := by
    simpa [prefixWord, tailWord_4973611, baseEnd_4973611] using wordTrace_append hprefix tailTrace_4973611
  have hstable : (prefixWord ++ tailWord_4973611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4973611).length < 2 ^ (prefixWord ++ tailWord_4973611).sum := by decide
  have hdescent : baseEnd_4973611 < baseStart_4973611 := by decide
  rcases family_descends (prefixWord ++ tailWord_4973611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4973612 : List Nat := [2, 2, 1, 1, 1, 2, 5, 4, 1, 1, 3]
def baseStart_4973612 : Nat := 118140960795 + 4973612 * 2 ^ 59
def prefixEnd_4973612 : Nat := 4983230072969 + 3 ^ 40 * 4973612 * 2
def baseEnd_4973612 : Nat := 2553853544969699953876781

theorem tailTrace_4973612 : CollatzResearch.WordTrace tailWord_4973612 prefixEnd_4973612 2553853544969699953876781 := by
  unfold tailWord_4973612
  simp only [CollatzResearch.WordTrace]
  refine ⟨90701266228730312074253545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120935021638307082765671393 90701266228730312074253545)
  ·
    refine ⟨68025949671547734055690159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90701266228730312074253545 68025949671547734055690159)
    ·
      refine ⟨102038924507321601083535239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68025949671547734055690159 102038924507321601083535239)
      ·
        refine ⟨153058386760982401625302859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102038924507321601083535239 153058386760982401625302859)
        ·
          refine ⟨229587580141473602437954289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153058386760982401625302859 229587580141473602437954289)
          ·
            refine ⟨172190685106105201828465717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 229587580141473602437954289 172190685106105201828465717)
            ·
              refine ⟨16142876728697362671418661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 172190685106105201828465717 16142876728697362671418661)
              ·
                refine ⟨3026789386630755500890999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16142876728697362671418661 3026789386630755500890999)
                ·
                  refine ⟨4540184079946133251336499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3026789386630755500890999 4540184079946133251336499)
                  ·
                    refine ⟨6810276119919199877004749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4540184079946133251336499 6810276119919199877004749)
                    ·
                      refine ⟨2553853544969699953876781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6810276119919199877004749 2553853544969699953876781)
                      ·
                        rfl

theorem cell23_4973612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 4, 1, 1, 3].length) (baseStart_4973612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4973612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4973612 prefixEnd_4973612 := by exact prefixLift 4973612
  have htrace : WordTrace (prefixWord ++ tailWord_4973612) baseStart_4973612 baseEnd_4973612 := by
    simpa [prefixWord, tailWord_4973612, baseEnd_4973612] using wordTrace_append hprefix tailTrace_4973612
  have hstable : (prefixWord ++ tailWord_4973612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4973612).length < 2 ^ (prefixWord ++ tailWord_4973612).sum := by decide
  have hdescent : baseEnd_4973612 < baseStart_4973612 := by decide
  rcases family_descends (prefixWord ++ tailWord_4973612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4973618 : List Nat := [3, 2, 1, 1, 2, 2, 1, 1, 5, 1, 4]
def baseStart_4973618 : Nat := 118140960795 + 4973618 * 2 ^ 59
def prefixEnd_4973618 : Nat := 4983230072969 + 3 ^ 40 * 4973618 * 2
def baseEnd_4973618 : Nat := 2553856625853626930401753

theorem tailTrace_4973618 : CollatzResearch.WordTrace tailWord_4973618 prefixEnd_4973618 2553856625853626930401753 := by
  unfold tailWord_4973618
  simp only [CollatzResearch.WordTrace]
  refine ⟨45350687823859721793306377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120935167530292591448817005 45350687823859721793306377)
  ·
    refine ⟨34013015867894791344979783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45350687823859721793306377 34013015867894791344979783)
    ·
      refine ⟨51019523801842187017469675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34013015867894791344979783 51019523801842187017469675)
      ·
        refine ⟨76529285702763280526204513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51019523801842187017469675 76529285702763280526204513)
        ·
          refine ⟨57396964277072460394653385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76529285702763280526204513 57396964277072460394653385)
          ·
            refine ⟨43047723207804345295990039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57396964277072460394653385 43047723207804345295990039)
            ·
              refine ⟨64571584811706517943985059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43047723207804345295990039 64571584811706517943985059)
              ·
                refine ⟨96857377217559776915977589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64571584811706517943985059 96857377217559776915977589)
                ·
                  refine ⟨9080379114146229085872899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 96857377217559776915977589 9080379114146229085872899)
                  ·
                    refine ⟨13620568671219343628809349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9080379114146229085872899 13620568671219343628809349)
                    ·
                      refine ⟨2553856625853626930401753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13620568671219343628809349 2553856625853626930401753)
                      ·
                        rfl

theorem cell23_4973618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 5, 1, 4].length) (baseStart_4973618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4973618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4973618 prefixEnd_4973618 := by exact prefixLift 4973618
  have htrace : WordTrace (prefixWord ++ tailWord_4973618) baseStart_4973618 baseEnd_4973618 := by
    simpa [prefixWord, tailWord_4973618, baseEnd_4973618] using wordTrace_append hprefix tailTrace_4973618
  have hstable : (prefixWord ++ tailWord_4973618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4973618).length < 2 ^ (prefixWord ++ tailWord_4973618).sum := by decide
  have hdescent : baseEnd_4973618 < baseStart_4973618 := by decide
  rcases family_descends (prefixWord ++ tailWord_4973618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4973628 : List Nat := [2, 2, 2, 2, 2, 2, 1, 3, 1, 6]
def baseStart_4973628 : Nat := 118140960795 + 4973628 * 2 ^ 59
def prefixEnd_4973628 : Nat := 4983230072969 + 3 ^ 40 * 4973628 * 2
def baseEnd_4973628 : Nat := 851287253553390630425569

theorem tailTrace_4973628 : CollatzResearch.WordTrace tailWord_4973628 prefixEnd_4973628 851287253553390630425569 := by
  unfold tailWord_4973628
  simp only [CollatzResearch.WordTrace]
  refine ⟨90701558012701329440544769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120935410683601772587393025 90701558012701329440544769)
  ·
    refine ⟨68026168509525997080408577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90701558012701329440544769 68026168509525997080408577)
    ·
      refine ⟨51019626382144497810306433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68026168509525997080408577 51019626382144497810306433)
      ·
        refine ⟨38264719786608373357729825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51019626382144497810306433 38264719786608373357729825)
        ·
          refine ⟨28698539839956280018297369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38264719786608373357729825 28698539839956280018297369)
          ·
            refine ⟨21523904879967210013723027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28698539839956280018297369 21523904879967210013723027)
            ·
              refine ⟨32285857319950815020584541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21523904879967210013723027 32285857319950815020584541)
              ·
                refine ⟨12107196494981555632719203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32285857319950815020584541 12107196494981555632719203)
                ·
                  refine ⟨18160794742472333449078805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12107196494981555632719203 18160794742472333449078805)
                  ·
                    refine ⟨851287253553390630425569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18160794742472333449078805 851287253553390630425569)
                    ·
                      rfl

theorem cell23_4973628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 3, 1, 6].length) (baseStart_4973628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4973628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4973628 prefixEnd_4973628 := by exact prefixLift 4973628
  have htrace : WordTrace (prefixWord ++ tailWord_4973628) baseStart_4973628 baseEnd_4973628 := by
    simpa [prefixWord, tailWord_4973628, baseEnd_4973628] using wordTrace_append hprefix tailTrace_4973628
  have hstable : (prefixWord ++ tailWord_4973628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4973628).length < 2 ^ (prefixWord ++ tailWord_4973628).sum := by decide
  have hdescent : baseEnd_4973628 < baseStart_4973628 := by decide
  rcases family_descends (prefixWord ++ tailWord_4973628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4973645 : List Nat := [1, 6, 1, 1, 1, 2, 2, 2, 1, 6]
def baseStart_4973645 : Nat := 118140960795 + 4973645 * 2 ^ 59
def prefixEnd_4973645 : Nat := 4983230072969 + 3 ^ 40 * 4973645 * 2
def baseEnd_4973645 : Nat := 851290163277099441588043

theorem tailTrace_4973645 : CollatzResearch.WordTrace tailWord_4973645 prefixEnd_4973645 851290163277099441588043 := by
  unfold tailWord_4973645
  simp only [CollatzResearch.WordTrace]
  refine ⟨181403736066341070784458389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120935824044227380522972259 181403736066341070784458389)
  ·
    refine ⟨8503300128109737693021487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 181403736066341070784458389 8503300128109737693021487)
    ·
      refine ⟨12754950192164606539532231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8503300128109737693021487 12754950192164606539532231)
      ·
        refine ⟨19132425288246909809298347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12754950192164606539532231 19132425288246909809298347)
        ·
          refine ⟨28698637932370364713947521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19132425288246909809298347 28698637932370364713947521)
          ·
            refine ⟨21523978449277773535460641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28698637932370364713947521 21523978449277773535460641)
            ·
              refine ⟨16142983836958330151595481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21523978449277773535460641 16142983836958330151595481)
              ·
                refine ⟨12107237877718747613696611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16142983836958330151595481 12107237877718747613696611)
                ·
                  refine ⟨18160856816578121420544917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12107237877718747613696611 18160856816578121420544917)
                  ·
                    refine ⟨851290163277099441588043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18160856816578121420544917 851290163277099441588043)
                    ·
                      rfl

theorem cell23_4973645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_4973645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4973645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4973645 prefixEnd_4973645 := by exact prefixLift 4973645
  have htrace : WordTrace (prefixWord ++ tailWord_4973645) baseStart_4973645 baseEnd_4973645 := by
    simpa [prefixWord, tailWord_4973645, baseEnd_4973645] using wordTrace_append hprefix tailTrace_4973645
  have hstable : (prefixWord ++ tailWord_4973645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4973645).length < 2 ^ (prefixWord ++ tailWord_4973645).sum := by decide
  have hdescent : baseEnd_4973645 < baseStart_4973645 := by decide
  rcases family_descends (prefixWord ++ tailWord_4973645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4973652 : List Nat := [2, 4, 1, 1, 1, 1, 6, 1, 1, 1, 4]
def baseStart_4973652 : Nat := 118140960795 + 4973652 * 2 ^ 59
def prefixEnd_4973652 : Nat := 4983230072969 + 3 ^ 40 * 4973652 * 2
def baseEnd_4973652 : Nat := 2553874084195879797376597

theorem tailTrace_4973652 : CollatzResearch.WordTrace tailWord_4973652 prefixEnd_4973652 2553874084195879797376597 := by
  unfold tailWord_4973652
  simp only [CollatzResearch.WordTrace]
  refine ⟨90701995688657855489981605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120935994251543807319975473 90701995688657855489981605)
  ·
    refine ⟨17006624191623347904371551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90701995688657855489981605 17006624191623347904371551)
    ·
      refine ⟨25509936287435021856557327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17006624191623347904371551 25509936287435021856557327)
      ·
        refine ⟨38264904431152532784835991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25509936287435021856557327 38264904431152532784835991)
        ·
          refine ⟨57397356646728799177253987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38264904431152532784835991 57397356646728799177253987)
          ·
            refine ⟨86096034970093198765880981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57397356646728799177253987 86096034970093198765880981)
            ·
              refine ⟨4035751639223118692150671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 86096034970093198765880981 4035751639223118692150671)
              ·
                refine ⟨6053627458834678038226007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4035751639223118692150671 6053627458834678038226007)
                ·
                  refine ⟨9080441188252017057339011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6053627458834678038226007 9080441188252017057339011)
                  ·
                    refine ⟨13620661782378025586008517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9080441188252017057339011 13620661782378025586008517)
                    ·
                      refine ⟨2553874084195879797376597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13620661782378025586008517 2553874084195879797376597)
                      ·
                        rfl

theorem cell23_4973652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 6, 1, 1, 1, 4].length) (baseStart_4973652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4973652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4973652 prefixEnd_4973652 := by exact prefixLift 4973652
  have htrace : WordTrace (prefixWord ++ tailWord_4973652) baseStart_4973652 baseEnd_4973652 := by
    simpa [prefixWord, tailWord_4973652, baseEnd_4973652] using wordTrace_append hprefix tailTrace_4973652
  have hstable : (prefixWord ++ tailWord_4973652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4973652).length < 2 ^ (prefixWord ++ tailWord_4973652).sum := by decide
  have hdescent : baseEnd_4973652 < baseStart_4973652 := by decide
  rcases family_descends (prefixWord ++ tailWord_4973652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4973669 : List Nat := [1, 3, 1, 3, 2, 1, 1, 6, 1, 2, 2]
def baseStart_4973669 : Nat := 118140960795 + 4973669 * 2 ^ 59
def prefixEnd_4973669 : Nat := 4983230072969 + 3 ^ 40 * 4973669 * 2
def baseEnd_4973669 : Nat := 2553882813367006230864019

theorem tailTrace_4973669 : CollatzResearch.WordTrace tailWord_4973669 prefixEnd_4973669 2553882813367006230864019 := by
  unfold tailWord_4973669
  simp only [CollatzResearch.WordTrace]
  refine ⟨181404611418254122883332061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120936407612169415255554707 181404611418254122883332061)
  ·
    refine ⟨68026729281845296081249523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181404611418254122883332061 68026729281845296081249523)
    ·
      refine ⟨102040093922767944121874285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68026729281845296081249523 102040093922767944121874285)
      ·
        refine ⟨38265035221037979045702857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102040093922767944121874285 38265035221037979045702857)
        ·
          refine ⟨28698776415778484284277143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38265035221037979045702857 28698776415778484284277143)
          ·
            refine ⟨43048164623667726426415715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28698776415778484284277143 43048164623667726426415715)
            ·
              refine ⟨64572246935501589639623573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43048164623667726426415715 64572246935501589639623573)
              ·
                refine ⟨3026824075101637014357355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 64572246935501589639623573 3026824075101637014357355)
                ·
                  refine ⟨4540236112652455521536033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3026824075101637014357355 4540236112652455521536033)
                  ·
                    refine ⟨3405177084489341641152025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4540236112652455521536033 3405177084489341641152025)
                    ·
                      refine ⟨2553882813367006230864019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3405177084489341641152025 2553882813367006230864019)
                      ·
                        rfl

theorem cell23_4973669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 6, 1, 2, 2].length) (baseStart_4973669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4973669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4973669 prefixEnd_4973669 := by exact prefixLift 4973669
  have htrace : WordTrace (prefixWord ++ tailWord_4973669) baseStart_4973669 baseEnd_4973669 := by
    simpa [prefixWord, tailWord_4973669, baseEnd_4973669] using wordTrace_append hprefix tailTrace_4973669
  have hstable : (prefixWord ++ tailWord_4973669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4973669).length < 2 ^ (prefixWord ++ tailWord_4973669).sum := by decide
  have hdescent : baseEnd_4973669 < baseStart_4973669 := by decide
  rcases family_descends (prefixWord ++ tailWord_4973669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4973672 : List Nat := [2, 1, 4, 4, 1, 1, 1, 2, 1, 1, 5]
def baseStart_4973672 : Nat := 118140960795 + 4973672 * 2 ^ 59
def prefixEnd_4973672 : Nat := 4983230072969 + 3 ^ 40 * 4973672 * 2
def baseEnd_4973672 : Nat := 2553884353808969719126505

theorem tailTrace_4973672 : CollatzResearch.WordTrace tailWord_4973672 prefixEnd_4973672 2553884353808969719126505 := by
  unfold tailWord_4973672
  simp only [CollatzResearch.WordTrace]
  refine ⟨90702360418621627197845635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120936480558162169597127513 90702360418621627197845635)
  ·
    refine ⟨136053540627932440796768453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90702360418621627197845635 136053540627932440796768453)
    ·
      refine ⟨25510038867737332649394085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 136053540627932440796768453 25510038867737332649394085)
      ·
        refine ⟨4783132287700749871761391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25510038867737332649394085 4783132287700749871761391)
        ·
          refine ⟨7174698431551124807642087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4783132287700749871761391 7174698431551124807642087)
          ·
            refine ⟨10762047647326687211463131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7174698431551124807642087 10762047647326687211463131)
            ·
              refine ⟨16143071470990030817194697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10762047647326687211463131 16143071470990030817194697)
              ·
                refine ⟨12107303603242523112896023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16143071470990030817194697 12107303603242523112896023)
                ·
                  refine ⟨18160955404863784669344035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12107303603242523112896023 18160955404863784669344035)
                  ·
                    refine ⟨27241433107295677004016053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18160955404863784669344035 27241433107295677004016053)
                    ·
                      refine ⟨2553884353808969719126505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27241433107295677004016053 2553884353808969719126505)
                      ·
                        rfl

theorem cell23_4973672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_4973672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4973672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4973672 prefixEnd_4973672 := by exact prefixLift 4973672
  have htrace : WordTrace (prefixWord ++ tailWord_4973672) baseStart_4973672 baseEnd_4973672 := by
    simpa [prefixWord, tailWord_4973672, baseEnd_4973672] using wordTrace_append hprefix tailTrace_4973672
  have hstable : (prefixWord ++ tailWord_4973672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4973672).length < 2 ^ (prefixWord ++ tailWord_4973672).sum := by decide
  have hdescent : baseEnd_4973672 < baseStart_4973672 := by decide
  rcases family_descends (prefixWord ++ tailWord_4973672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4973728 : List Nat := [2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 5]
def baseStart_4973728 : Nat := 118140960795 + 4973728 * 2 ^ 59
def prefixEnd_4973728 : Nat := 4983230072969 + 3 ^ 40 * 4973728 * 2
def baseEnd_4973728 : Nat := 2553913108725621500026247

theorem tailTrace_4973728 : CollatzResearch.WordTrace tailWord_4973728 prefixEnd_4973728 2553913108725621500026247 := by
  unfold tailWord_4973728
  simp only [CollatzResearch.WordTrace]
  refine ⟨90703381662520187979864919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120937842216693583973153225 90703381662520187979864919)
  ·
    refine ⟨136055072493780281969797379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90703381662520187979864919 136055072493780281969797379)
    ·
      refine ⟨204082608740670422954696069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136055072493780281969797379 204082608740670422954696069)
      ·
        refine ⟨38265489138875704304005513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 204082608740670422954696069 38265489138875704304005513)
        ·
          refine ⟨28699116854156778228004135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38265489138875704304005513 28699116854156778228004135)
          ·
            refine ⟨43048675281235167342006203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28699116854156778228004135 43048675281235167342006203)
            ·
              refine ⟨64573012921852751013009305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43048675281235167342006203 64573012921852751013009305)
              ·
                refine ⟨48429759691389563259756979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64573012921852751013009305 48429759691389563259756979)
                ·
                  refine ⟨72644639537084344889635469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48429759691389563259756979 72644639537084344889635469)
                  ·
                    refine ⟨27241739826406629333613301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 72644639537084344889635469 27241739826406629333613301)
                    ·
                      refine ⟨2553913108725621500026247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27241739826406629333613301 2553913108725621500026247)
                      ·
                        rfl

theorem cell23_4973728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_4973728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4973728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4973728 prefixEnd_4973728 := by exact prefixLift 4973728
  have htrace : WordTrace (prefixWord ++ tailWord_4973728) baseStart_4973728 baseEnd_4973728 := by
    simpa [prefixWord, tailWord_4973728, baseEnd_4973728] using wordTrace_append hprefix tailTrace_4973728
  have hstable : (prefixWord ++ tailWord_4973728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4973728).length < 2 ^ (prefixWord ++ tailWord_4973728).sum := by decide
  have hdescent : baseEnd_4973728 < baseStart_4973728 := by decide
  rcases family_descends (prefixWord ++ tailWord_4973728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4973745 : List Nat := [1, 2, 2, 5, 1, 1, 1, 2, 2, 1, 5]
def baseStart_4973745 : Nat := 118140960795 + 4973745 * 2 ^ 59
def prefixEnd_4973745 : Nat := 4983230072969 + 3 ^ 40 * 4973745 * 2
def baseEnd_4973745 : Nat := 2553921837896747933513669

theorem tailTrace_4973745 : CollatzResearch.WordTrace tailWord_4973745 prefixEnd_4973745 2553921837896747933513669 := by
  unfold tailWord_4973745
  simp only [CollatzResearch.WordTrace]
  refine ⟨181407383365978787863098689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120938255577319191908732459 181407383365978787863098689)
  ·
    refine ⟨136055537524484090897324017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181407383365978787863098689 136055537524484090897324017)
    ·
      refine ⟨102041653143363068172993013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136055537524484090897324017 102041653143363068172993013)
      ·
        refine ⟨9566404982190287641218095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 102041653143363068172993013 9566404982190287641218095)
        ·
          refine ⟨14349607473285431461827143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9566404982190287641218095 14349607473285431461827143)
          ·
            refine ⟨21524411209928147192740715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14349607473285431461827143 21524411209928147192740715)
            ·
              refine ⟨32286616814892220789111073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21524411209928147192740715 32286616814892220789111073)
              ·
                refine ⟨24214962611169165591833305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32286616814892220789111073 24214962611169165591833305)
                ·
                  refine ⟨18161221958376874193874979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24214962611169165591833305 18161221958376874193874979)
                  ·
                    refine ⟨27241832937565311290812469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18161221958376874193874979 27241832937565311290812469)
                    ·
                      refine ⟨2553921837896747933513669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27241832937565311290812469 2553921837896747933513669)
                      ·
                        rfl

theorem cell23_4973745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_4973745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4973745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4973745 prefixEnd_4973745 := by exact prefixLift 4973745
  have htrace : WordTrace (prefixWord ++ tailWord_4973745) baseStart_4973745 baseEnd_4973745 := by
    simpa [prefixWord, tailWord_4973745, baseEnd_4973745] using wordTrace_append hprefix tailTrace_4973745
  have hstable : (prefixWord ++ tailWord_4973745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4973745).length < 2 ^ (prefixWord ++ tailWord_4973745).sum := by decide
  have hdescent : baseEnd_4973745 < baseStart_4973745 := by decide
  rcases family_descends (prefixWord ++ tailWord_4973745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4973765 : List Nat := [1, 3, 1, 1, 1, 1, 3, 7, 5]
def baseStart_4973765 : Nat := 118140960795 + 4973765 * 2 ^ 59
def prefixEnd_4973765 : Nat := 4983230072969 + 3 ^ 40 * 4973765 * 2
def baseEnd_4973765 : Nat := 283770234167759761695953

theorem tailTrace_4973765 : CollatzResearch.WordTrace tailWord_4973765 prefixEnd_4973765 283770234167759761695953 := by
  unfold tailWord_4973765
  simp only [CollatzResearch.WordTrace]
  refine ⟨181408112825906331278826749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120938741883937554185884499 181408112825906331278826749)
  ·
    refine ⟨68028042309714874229560031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181408112825906331278826749 68028042309714874229560031)
    ·
      refine ⟨102042063464572311344340047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68028042309714874229560031 102042063464572311344340047)
      ·
        refine ⟨153063095196858467016510071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102042063464572311344340047 153063095196858467016510071)
        ·
          refine ⟨229594642795287700524765107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153063095196858467016510071 229594642795287700524765107)
          ·
            refine ⟨344391964192931550787147661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229594642795287700524765107 344391964192931550787147661)
            ·
              refine ⟨129146986572349331545180373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 344391964192931550787147661 129146986572349331545180373)
              ·
                refine ⟨3026882497789437458090165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 129146986572349331545180373 3026882497789437458090165)
                ·
                  refine ⟨283770234167759761695953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3026882497789437458090165 283770234167759761695953)
                  ·
                    rfl

theorem cell23_4973765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 7, 5].length) (baseStart_4973765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4973765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4973765 prefixEnd_4973765 := by exact prefixLift 4973765
  have htrace : WordTrace (prefixWord ++ tailWord_4973765) baseStart_4973765 baseEnd_4973765 := by
    simpa [prefixWord, tailWord_4973765, baseEnd_4973765] using wordTrace_append hprefix tailTrace_4973765
  have hstable : (prefixWord ++ tailWord_4973765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4973765).length < 2 ^ (prefixWord ++ tailWord_4973765).sum := by decide
  have hdescent : baseEnd_4973765 < baseStart_4973765 := by decide
  rcases family_descends (prefixWord ++ tailWord_4973765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4973869 : List Nat := [1, 5, 3, 1, 1, 1, 2, 1, 1, 4, 3]
def baseStart_4973869 : Nat := 118140960795 + 4973869 * 2 ^ 59
def prefixEnd_4973869 : Nat := 4983230072969 + 3 ^ 40 * 4973869 * 2
def baseEnd_4973869 : Nat := 2553985509497905448363099

theorem tailTrace_4973869 : CollatzResearch.WordTrace tailWord_4973869 prefixEnd_4973869 2553985509497905448363099 := by
  unfold tailWord_4973869
  simp only [CollatzResearch.WordTrace]
  refine ⟨181411906017529557040612661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120941270678353038027075107 181411906017529557040612661)
  ·
    refine ⟨17007366189143395972557437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 181411906017529557040612661 17007366189143395972557437)
    ·
      refine ⟨6377762320928773489709039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17007366189143395972557437 6377762320928773489709039)
      ·
        refine ⟨9566643481393160234563559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6377762320928773489709039 9566643481393160234563559)
        ·
          refine ⟨14349965222089740351845339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9566643481393160234563559 14349965222089740351845339)
          ·
            refine ⟨21524947833134610527768009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14349965222089740351845339 21524947833134610527768009)
            ·
              refine ⟨16143710874850957895826007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21524947833134610527768009 16143710874850957895826007)
              ·
                refine ⟨24215566312276436843739011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16143710874850957895826007 24215566312276436843739011)
                ·
                  refine ⟨36323349468414655265608517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24215566312276436843739011 36323349468414655265608517)
                  ·
                    refine ⟨6810628025327747862301597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36323349468414655265608517 6810628025327747862301597)
                    ·
                      refine ⟨2553985509497905448363099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6810628025327747862301597 2553985509497905448363099)
                      ·
                        rfl

theorem cell23_4973869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_4973869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4973869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4973869 prefixEnd_4973869 := by exact prefixLift 4973869
  have htrace : WordTrace (prefixWord ++ tailWord_4973869) baseStart_4973869 baseEnd_4973869 := by
    simpa [prefixWord, tailWord_4973869, baseEnd_4973869] using wordTrace_append hprefix tailTrace_4973869
  have hstable : (prefixWord ++ tailWord_4973869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4973869).length < 2 ^ (prefixWord ++ tailWord_4973869).sum := by decide
  have hdescent : baseEnd_4973869 < baseStart_4973869 := by decide
  rcases family_descends (prefixWord ++ tailWord_4973869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4973932 : List Nat := [2, 2, 1, 1, 5, 2, 1, 2, 1, 6]
def baseStart_4973932 : Nat := 118140960795 + 4973932 * 2 ^ 59
def prefixEnd_4973932 : Nat := 4983230072969 + 3 ^ 40 * 4973932 * 2
def baseEnd_4973932 : Nat := 851339286259712900625103

theorem tailTrace_4973932 : CollatzResearch.WordTrace tailWord_4973932 prefixEnd_4973932 851339286259712900625103 := by
  unfold tailWord_4973932
  simp only [CollatzResearch.WordTrace]
  refine ⟨90707101908150659400078025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120942802544200879200104033 90707101908150659400078025)
  ·
    refine ⟨68030326431112994550058519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90707101908150659400078025 68030326431112994550058519)
    ·
      refine ⟨102045489646669491825087779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68030326431112994550058519 102045489646669491825087779)
      ·
        refine ⟨153068234470004237737631669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102045489646669491825087779 153068234470004237737631669)
        ·
          refine ⟨14350146981562897287902969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 153068234470004237737631669 14350146981562897287902969)
          ·
            refine ⟨10762610236172172965927227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14350146981562897287902969 10762610236172172965927227)
            ·
              refine ⟨16143915354258259448890841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10762610236172172965927227 16143915354258259448890841)
              ·
                refine ⟨12107936515693694586668131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16143915354258259448890841 12107936515693694586668131)
                ·
                  refine ⟨18161904773540541880002197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12107936515693694586668131 18161904773540541880002197)
                  ·
                    refine ⟨851339286259712900625103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18161904773540541880002197 851339286259712900625103)
                    ·
                      rfl

theorem cell23_4973932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 6].length) (baseStart_4973932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4973932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4973932 prefixEnd_4973932 := by exact prefixLift 4973932
  have htrace : WordTrace (prefixWord ++ tailWord_4973932) baseStart_4973932 baseEnd_4973932 := by
    simpa [prefixWord, tailWord_4973932, baseEnd_4973932] using wordTrace_append hprefix tailTrace_4973932
  have hstable : (prefixWord ++ tailWord_4973932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4973932).length < 2 ^ (prefixWord ++ tailWord_4973932).sum := by decide
  have hdescent : baseEnd_4973932 < baseStart_4973932 := by decide
  rcases family_descends (prefixWord ++ tailWord_4973932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4973949 : List Nat := [1, 4, 1, 1, 2, 2, 4, 2, 2, 4]
def baseStart_4973949 : Nat := 118140960795 + 4973949 * 2 ^ 59
def prefixEnd_4973949 : Nat := 4983230072969 + 3 ^ 40 * 4973949 * 2
def baseEnd_4973949 : Nat := 851342195983421711787577

theorem tailTrace_4973949 : CollatzResearch.WordTrace tailWord_4973949 prefixEnd_4973949 851342195983421711787577 := by
  unfold tailWord_4973949
  simp only [CollatzResearch.WordTrace]
  refine ⟨181414823857239730703524901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120943215904826487135683267 181414823857239730703524901)
  ·
    refine ⟨34015279473232449506910919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 181414823857239730703524901 34015279473232449506910919)
    ·
      refine ⟨51022919209848674260366379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34015279473232449506910919 51022919209848674260366379)
      ·
        refine ⟨76534378814773011390549569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51022919209848674260366379 76534378814773011390549569)
        ·
          refine ⟨57400784111079758542912177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76534378814773011390549569 57400784111079758542912177)
          ·
            refine ⟨43050588083309818907184133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57400784111079758542912177 43050588083309818907184133)
            ·
              refine ⟨8071985265620591045097025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43050588083309818907184133 8071985265620591045097025)
              ·
                refine ⟨6053988949215443283822769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8071985265620591045097025 6053988949215443283822769)
                ·
                  refine ⟨4540491711911582462867077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6053988949215443283822769 4540491711911582462867077)
                  ·
                    refine ⟨851342195983421711787577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4540491711911582462867077 851342195983421711787577)
                    ·
                      rfl

theorem cell23_4973949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 2, 2, 4].length) (baseStart_4973949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4973949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4973949 prefixEnd_4973949 := by exact prefixLift 4973949
  have htrace : WordTrace (prefixWord ++ tailWord_4973949) baseStart_4973949 baseEnd_4973949 := by
    simpa [prefixWord, tailWord_4973949, baseEnd_4973949] using wordTrace_append hprefix tailTrace_4973949
  have hstable : (prefixWord ++ tailWord_4973949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4973949).length < 2 ^ (prefixWord ++ tailWord_4973949).sum := by decide
  have hdescent : baseEnd_4973949 < baseStart_4973949 := by decide
  rcases family_descends (prefixWord ++ tailWord_4973949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4973975 : List Nat := [1, 1, 3, 3, 1, 1, 1, 1, 4, 7]
def baseStart_4973975 : Nat := 118140960795 + 4973975 * 2 ^ 59
def prefixEnd_4973975 : Nat := 4983230072969 + 3 ^ 40 * 4973975 * 2
def baseEnd_4973975 : Nat := 851346646149094011212537

theorem tailTrace_4973975 : CollatzResearch.WordTrace tailWord_4973975 prefixEnd_4973975 851346646149094011212537 := by
  unfold tailWord_4973975
  simp only [CollatzResearch.WordTrace]
  refine ⟨181415772155145537143971379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120943848103430358095980919 181415772155145537143971379)
  ·
    refine ⟨272123658232718305715957069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181415772155145537143971379 272123658232718305715957069)
    ·
      refine ⟨102046371837269364643483901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 272123658232718305715957069 102046371837269364643483901)
      ·
        refine ⟨38267389438976011741306463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102046371837269364643483901 38267389438976011741306463)
        ·
          refine ⟨57401084158464017611959695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38267389438976011741306463 57401084158464017611959695)
          ·
            refine ⟨86101626237696026417939543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57401084158464017611959695 86101626237696026417939543)
            ·
              refine ⟨129152439356544039626909315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86101626237696026417939543 129152439356544039626909315)
              ·
                refine ⟨193728659034816059440363973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129152439356544039626909315 193728659034816059440363973)
                ·
                  refine ⟨36324123569028011145068245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 193728659034816059440363973 36324123569028011145068245)
                  ·
                    refine ⟨851346646149094011212537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36324123569028011145068245 851346646149094011212537)
                    ·
                      rfl

theorem cell23_4973975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 7].length) (baseStart_4973975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4973975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4973975 prefixEnd_4973975 := by exact prefixLift 4973975
  have htrace : WordTrace (prefixWord ++ tailWord_4973975) baseStart_4973975 baseEnd_4973975 := by
    simpa [prefixWord, tailWord_4973975, baseEnd_4973975] using wordTrace_append hprefix tailTrace_4973975
  have hstable : (prefixWord ++ tailWord_4973975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4973975).length < 2 ^ (prefixWord ++ tailWord_4973975).sum := by decide
  have hdescent : baseEnd_4973975 < baseStart_4973975 := by decide
  rcases family_descends (prefixWord ++ tailWord_4973975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4974062 : List Nat := [4, 1, 2, 1, 2, 1, 1, 1, 1, 2, 7]
def baseStart_4974062 : Nat := 118140960795 + 4974062 * 2 ^ 59
def prefixEnd_4974062 : Nat := 4983230072969 + 3 ^ 40 * 4974062 * 2
def baseEnd_4974062 : Nat := 2554084611264223193249711

theorem tailTrace_4974062 : CollatzResearch.WordTrace tailWord_4974062 prefixEnd_4974062 2554084611264223193249711 := by
  unfold tailWord_4974062
  simp only [CollatzResearch.WordTrace]
  refine ⟨22677368163228793875298555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120945963537220234001592293 22677368163228793875298555)
  ·
    refine ⟨34016052244843190812947833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22677368163228793875298555 34016052244843190812947833)
    ·
      refine ⟨25512039183632393109710875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34016052244843190812947833 25512039183632393109710875)
      ·
        refine ⟨38268058775448589664566313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25512039183632393109710875 38268058775448589664566313)
        ·
          refine ⟨28701044081586442248424735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38268058775448589664566313 28701044081586442248424735)
          ·
            refine ⟨43051566122379663372637103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28701044081586442248424735 43051566122379663372637103)
            ·
              refine ⟨64577349183569495058955655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43051566122379663372637103 64577349183569495058955655)
              ·
                refine ⟨96866023775354242588433483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64577349183569495058955655 96866023775354242588433483)
                ·
                  refine ⟨145299035663031363882650225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96866023775354242588433483 145299035663031363882650225)
                  ·
                    refine ⟨108974276747273522911987669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 145299035663031363882650225 108974276747273522911987669)
                    ·
                      refine ⟨2554084611264223193249711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 108974276747273522911987669 2554084611264223193249711)
                      ·
                        rfl

theorem cell23_4974062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_4974062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4974062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4974062 prefixEnd_4974062 := by exact prefixLift 4974062
  have htrace : WordTrace (prefixWord ++ tailWord_4974062) baseStart_4974062 baseEnd_4974062 := by
    simpa [prefixWord, tailWord_4974062, baseEnd_4974062] using wordTrace_append hprefix tailTrace_4974062
  have hstable : (prefixWord ++ tailWord_4974062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4974062).length < 2 ^ (prefixWord ++ tailWord_4974062).sum := by decide
  have hdescent : baseEnd_4974062 < baseStart_4974062 := by decide
  rcases family_descends (prefixWord ++ tailWord_4974062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4974099 : List Nat := [1, 1, 1, 2, 1, 7, 2, 1, 2, 5]
def baseStart_4974099 : Nat := 118140960795 + 4974099 * 2 ^ 59
def prefixEnd_4974099 : Nat := 4983230072969 + 3 ^ 40 * 4974099 * 2
def baseEnd_4974099 : Nat := 851367870016146516162347

theorem tailTrace_4974099 : CollatzResearch.WordTrace tailWord_4974099 prefixEnd_4974099 851367870016146516162347 := by
  unfold tailWord_4974099
  simp only [CollatzResearch.WordTrace]
  refine ⟨181420294806696306321485351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120946863204464204214323567 181420294806696306321485351)
  ·
    refine ⟨272130442210044459482228027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181420294806696306321485351 272130442210044459482228027)
    ·
      refine ⟨408195663315066689223342041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272130442210044459482228027 408195663315066689223342041)
      ·
        refine ⟨306146747486300016917506531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 408195663315066689223342041 306146747486300016917506531)
        ·
          refine ⟨459220121229450025376259797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 306146747486300016917506531 459220121229450025376259797)
          ·
            refine ⟨10762971591315234969756089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 459220121229450025376259797 10762971591315234969756089)
            ·
              refine ⟨8072228693486426227317067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10762971591315234969756089 8072228693486426227317067)
              ·
                refine ⟨12108343040229639340975601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8072228693486426227317067 12108343040229639340975601)
                ·
                  refine ⟨9081257280172229505731701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12108343040229639340975601 9081257280172229505731701)
                  ·
                    refine ⟨851367870016146516162347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9081257280172229505731701 851367870016146516162347)
                    ·
                      rfl

theorem cell23_4974099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 1, 2, 5].length) (baseStart_4974099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4974099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4974099 prefixEnd_4974099 := by exact prefixLift 4974099
  have htrace : WordTrace (prefixWord ++ tailWord_4974099) baseStart_4974099 baseEnd_4974099 := by
    simpa [prefixWord, tailWord_4974099, baseEnd_4974099] using wordTrace_append hprefix tailTrace_4974099
  have hstable : (prefixWord ++ tailWord_4974099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4974099).length < 2 ^ (prefixWord ++ tailWord_4974099).sum := by decide
  have hdescent : baseEnd_4974099 < baseStart_4974099 := by decide
  rcases family_descends (prefixWord ++ tailWord_4974099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4974120 : List Nat := [2, 1, 5, 2, 2, 2, 2, 2, 5]
def baseStart_4974120 : Nat := 118140960795 + 4974120 * 2 ^ 59
def prefixEnd_4974120 : Nat := 4983230072969 + 3 ^ 40 * 4974120 * 2
def baseEnd_4974120 : Nat := 283790488126909329591605

theorem tailTrace_4974120 : CollatzResearch.WordTrace tailWord_4974120 prefixEnd_4974120 283790488126909329591605 := by
  unfold tailWord_4974120
  simp only [CollatzResearch.WordTrace]
  refine ⟨90710530369810113453999907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120947373826413484605333209 90710530369810113453999907)
  ·
    refine ⟨136065795554715170180999861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90710530369810113453999907 136065795554715170180999861)
    ·
      refine ⟨12756168333254547204468737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 136065795554715170180999861 12756168333254547204468737)
      ·
        refine ⟨9567126249940910403351553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12756168333254547204468737 9567126249940910403351553)
        ·
          refine ⟨7175344687455682802513665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9567126249940910403351553 7175344687455682802513665)
          ·
            refine ⟨5381508515591762101885249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7175344687455682802513665 5381508515591762101885249)
            ·
              refine ⟨4036131386693821576413937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5381508515591762101885249 4036131386693821576413937)
              ·
                refine ⟨3027098540020366182310453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4036131386693821576413937 3027098540020366182310453)
                ·
                  refine ⟨283790488126909329591605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3027098540020366182310453 283790488126909329591605)
                  ·
                    rfl

theorem cell23_4974120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 2, 2, 5].length) (baseStart_4974120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4974120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4974120 prefixEnd_4974120 := by exact prefixLift 4974120
  have htrace : WordTrace (prefixWord ++ tailWord_4974120) baseStart_4974120 baseEnd_4974120 := by
    simpa [prefixWord, tailWord_4974120, baseEnd_4974120] using wordTrace_append hprefix tailTrace_4974120
  have hstable : (prefixWord ++ tailWord_4974120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4974120).length < 2 ^ (prefixWord ++ tailWord_4974120).sum := by decide
  have hdescent : baseEnd_4974120 < baseStart_4974120 := by decide
  rcases family_descends (prefixWord ++ tailWord_4974120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4974129 : List Nat := [1, 2, 2, 3, 1, 1, 1, 5, 3, 4]
def baseStart_4974129 : Nat := 118140960795 + 4974129 * 2 ^ 59
def prefixEnd_4974129 : Nat := 4983230072969 + 3 ^ 40 * 4974129 * 2
def baseEnd_4974129 : Nat := 851373004822691477037301

theorem tailTrace_4974129 : CollatzResearch.WordTrace tailWord_4974129 prefixEnd_4974129 851373004822691477037301 := by
  unfold tailWord_4974129
  simp only [CollatzResearch.WordTrace]
  refine ⟨181421388996587621445077441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120947592664391747630051627 181421388996587621445077441)
  ·
    refine ⟨136066041747440716083808081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181421388996587621445077441 136066041747440716083808081)
    ·
      refine ⟨102049531310580537062856061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136066041747440716083808081 102049531310580537062856061)
      ·
        refine ⟨38268574241467701398571023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102049531310580537062856061 38268574241467701398571023)
        ·
          refine ⟨57402861362201552097856535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38268574241467701398571023 57402861362201552097856535)
          ·
            refine ⟨86104292043302328146784803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57402861362201552097856535 86104292043302328146784803)
            ·
              refine ⟨129156438064953492220177205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86104292043302328146784803 129156438064953492220177205)
              ·
                refine ⟨12108416068589389895641613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 129156438064953492220177205 12108416068589389895641613)
                ·
                  refine ⟨4540656025721021210865605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12108416068589389895641613 4540656025721021210865605)
                  ·
                    refine ⟨851373004822691477037301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4540656025721021210865605 851373004822691477037301)
                    ·
                      rfl

theorem cell23_4974129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 5, 3, 4].length) (baseStart_4974129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4974129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4974129 prefixEnd_4974129 := by exact prefixLift 4974129
  have htrace : WordTrace (prefixWord ++ tailWord_4974129) baseStart_4974129 baseEnd_4974129 := by
    simpa [prefixWord, tailWord_4974129, baseEnd_4974129] using wordTrace_append hprefix tailTrace_4974129
  have hstable : (prefixWord ++ tailWord_4974129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4974129).length < 2 ^ (prefixWord ++ tailWord_4974129).sum := by decide
  have hdescent : baseEnd_4974129 < baseStart_4974129 := by decide
  rcases family_descends (prefixWord ++ tailWord_4974129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4974136 : List Nat := [2, 1, 2, 1, 4, 3, 1, 1, 2, 4, 2]
def baseStart_4974136 : Nat := 118140960795 + 4974136 * 2 ^ 59
def prefixEnd_4974136 : Nat := 4983230072969 + 3 ^ 40 * 4974136 * 2
def baseEnd_4974136 : Nat := 2554122608832655903724371

theorem tailTrace_4974136 : CollatzResearch.WordTrace tailWord_4974136 prefixEnd_4974136 2554122608832655903724371 := by
  unfold tailWord_4974136
  simp only [CollatzResearch.WordTrace]
  refine ⟨90710822153781130820291131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120947762871708174427054841 90710822153781130820291131)
  ·
    refine ⟨136066233230671696230436697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90710822153781130820291131 136066233230671696230436697)
    ·
      refine ⟨102049674923003772172827523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136066233230671696230436697 102049674923003772172827523)
      ·
        refine ⟨153074512384505658259241285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102049674923003772172827523 153074512384505658259241285)
        ·
          refine ⟨28701471072094810923607741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 153074512384505658259241285 28701471072094810923607741)
          ·
            refine ⟨10763051652035554096352903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28701471072094810923607741 10763051652035554096352903)
            ·
              refine ⟨16144577478053331144529355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10763051652035554096352903 16144577478053331144529355)
              ·
                refine ⟨24216866217079996716794033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16144577478053331144529355 24216866217079996716794033)
                ·
                  refine ⟨18162649662809997537595525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24216866217079996716794033 18162649662809997537595525)
                  ·
                    refine ⟨3405496811776874538299161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18162649662809997537595525 3405496811776874538299161)
                    ·
                      refine ⟨2554122608832655903724371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3405496811776874538299161 2554122608832655903724371)
                      ·
                        rfl

theorem cell23_4974136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 2, 4, 2].length) (baseStart_4974136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4974136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4974136 prefixEnd_4974136 := by exact prefixLift 4974136
  have htrace : WordTrace (prefixWord ++ tailWord_4974136) baseStart_4974136 baseEnd_4974136 := by
    simpa [prefixWord, tailWord_4974136, baseEnd_4974136] using wordTrace_append hprefix tailTrace_4974136
  have hstable : (prefixWord ++ tailWord_4974136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4974136).length < 2 ^ (prefixWord ++ tailWord_4974136).sum := by decide
  have hdescent : baseEnd_4974136 < baseStart_4974136 := by decide
  rcases family_descends (prefixWord ++ tailWord_4974136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4974150 : List Nat := [6, 1, 1, 1, 3, 2, 1, 1, 2, 5]
def baseStart_4974150 : Nat := 118140960795 + 4974150 * 2 ^ 59
def prefixEnd_4974150 : Nat := 4983230072969 + 3 ^ 40 * 4974150 * 2
def baseEnd_4974150 : Nat := 851376599187272949649769

theorem tailTrace_4974150 : CollatzResearch.WordTrace tailWord_4974150 prefixEnd_4974150 851376599187272949649769 := by
  unfold tailWord_4974150
  simp only [CollatzResearch.WordTrace]
  refine ⟨5669442341547235688487247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 120948103286341028021061269 5669442341547235688487247)
  ·
    refine ⟨8504163512320853532730871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5669442341547235688487247 8504163512320853532730871)
    ·
      refine ⟨12756245268481280299096307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8504163512320853532730871 12756245268481280299096307)
      ·
        refine ⟨19134367902721920448644461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12756245268481280299096307 19134367902721920448644461)
        ·
          refine ⟨7175387963520720168241673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19134367902721920448644461 7175387963520720168241673)
          ·
            refine ⟨5381540972640540126181255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7175387963520720168241673 5381540972640540126181255)
            ·
              refine ⟨8072311458960810189271883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5381540972640540126181255 8072311458960810189271883)
              ·
                refine ⟨12108467188441215283907825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8072311458960810189271883 12108467188441215283907825)
                ·
                  refine ⟨9081350391330911462930869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12108467188441215283907825 9081350391330911462930869)
                  ·
                    refine ⟨851376599187272949649769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9081350391330911462930869 851376599187272949649769)
                    ·
                      rfl

theorem cell23_4974150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_4974150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4974150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4974150 prefixEnd_4974150 := by exact prefixLift 4974150
  have htrace : WordTrace (prefixWord ++ tailWord_4974150) baseStart_4974150 baseEnd_4974150 := by
    simpa [prefixWord, tailWord_4974150, baseEnd_4974150] using wordTrace_append hprefix tailTrace_4974150
  have hstable : (prefixWord ++ tailWord_4974150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4974150).length < 2 ^ (prefixWord ++ tailWord_4974150).sum := by decide
  have hdescent : baseEnd_4974150 < baseStart_4974150 := by decide
  rcases family_descends (prefixWord ++ tailWord_4974150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4974156 : List Nat := [2, 2, 1, 3, 1, 3, 3, 1, 2, 2, 3]
def baseStart_4974156 : Nat := 118140960795 + 4974156 * 2 ^ 59
def prefixEnd_4974156 : Nat := 4983230072969 + 3 ^ 40 * 4974156 * 2
def baseEnd_4974156 : Nat := 2554132878445745825474279

theorem tailTrace_4974156 : CollatzResearch.WordTrace tailWord_4974156 prefixEnd_4974156 2554132878445745825474279 := by
  unfold tailWord_4974156
  simp only [CollatzResearch.WordTrace]
  refine ⟨90711186883744902528155161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120948249178326536704206881 90711186883744902528155161)
  ·
    refine ⟨68033390162808676896116371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90711186883744902528155161 68033390162808676896116371)
    ·
      refine ⟨102050085244213015344174557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68033390162808676896116371 102050085244213015344174557)
      ·
        refine ⟨38268781966579880754065459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102050085244213015344174557 38268781966579880754065459)
        ·
          refine ⟨57403172949869821131098189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38268781966579880754065459 57403172949869821131098189)
          ·
            refine ⟨21526189856201182924161821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57403172949869821131098189 21526189856201182924161821)
            ·
              refine ⟨8072321196075443596560683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21526189856201182924161821 8072321196075443596560683)
              ·
                refine ⟨12108481794113165394841025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8072321196075443596560683 12108481794113165394841025)
                ·
                  refine ⟨9081361345584874046130769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12108481794113165394841025 9081361345584874046130769)
                  ·
                    refine ⟨6811021009188655534598077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9081361345584874046130769 6811021009188655534598077)
                    ·
                      refine ⟨2554132878445745825474279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6811021009188655534598077 2554132878445745825474279)
                      ·
                        rfl

theorem cell23_4974156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 1, 2, 2, 3].length) (baseStart_4974156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4974156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4974156 prefixEnd_4974156 := by exact prefixLift 4974156
  have htrace : WordTrace (prefixWord ++ tailWord_4974156) baseStart_4974156 baseEnd_4974156 := by
    simpa [prefixWord, tailWord_4974156, baseEnd_4974156] using wordTrace_append hprefix tailTrace_4974156
  have hstable : (prefixWord ++ tailWord_4974156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4974156).length < 2 ^ (prefixWord ++ tailWord_4974156).sum := by decide
  have hdescent : baseEnd_4974156 < baseStart_4974156 := by decide
  rcases family_descends (prefixWord ++ tailWord_4974156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4974219 : List Nat := [1, 1, 1, 1, 4, 1, 3, 1, 6, 4]
def baseStart_4974219 : Nat := 118140960795 + 4974219 * 2 ^ 59
def prefixEnd_4974219 : Nat := 4983230072969 + 3 ^ 40 * 4974219 * 2
def baseEnd_4974219 : Nat := 851388409242326359662163

theorem tailTrace_4974219 : CollatzResearch.WordTrace tailWord_4974219 prefixEnd_4974219 851388409242326359662163 := by
  unfold tailWord_4974219
  simp only [CollatzResearch.WordTrace]
  refine ⟨181424671566261566815853711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120949781044174377877235807 181424671566261566815853711)
  ·
    refine ⟨272137007349392350223780567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181424671566261566815853711 272137007349392350223780567)
    ·
      refine ⟨408205511024088525335670851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272137007349392350223780567 408205511024088525335670851)
      ·
        refine ⟨612308266536132788003506277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 408205511024088525335670851 612308266536132788003506277)
        ·
          refine ⟨114807799975524897750657427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 612308266536132788003506277 114807799975524897750657427)
          ·
            refine ⟨172211699963287346625986141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114807799975524897750657427 172211699963287346625986141)
            ·
              refine ⟨64579387486232754984744803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 172211699963287346625986141 64579387486232754984744803)
              ·
                refine ⟨96869081229349132477117205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64579387486232754984744803 96869081229349132477117205)
                ·
                  refine ⟨4540738182625740584864869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 96869081229349132477117205 4540738182625740584864869)
                  ·
                    refine ⟨851388409242326359662163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4540738182625740584864869 851388409242326359662163)
                    ·
                      rfl

theorem cell23_4974219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 6, 4].length) (baseStart_4974219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4974219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4974219 prefixEnd_4974219 := by exact prefixLift 4974219
  have htrace : WordTrace (prefixWord ++ tailWord_4974219) baseStart_4974219 baseEnd_4974219 := by
    simpa [prefixWord, tailWord_4974219, baseEnd_4974219] using wordTrace_append hprefix tailTrace_4974219
  have hstable : (prefixWord ++ tailWord_4974219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4974219).length < 2 ^ (prefixWord ++ tailWord_4974219).sum := by decide
  have hdescent : baseEnd_4974219 < baseStart_4974219 := by decide
  rcases family_descends (prefixWord ++ tailWord_4974219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4974253 : List Nat := [1, 5, 2, 1, 1, 1, 3, 3, 2, 4]
def baseStart_4974253 : Nat := 118140960795 + 4974253 * 2 ^ 59
def prefixEnd_4974253 : Nat := 4983230072969 + 3 ^ 40 * 4974253 * 2
def baseEnd_4974253 : Nat := 851394228689743981987111

theorem tailTrace_4974253 : CollatzResearch.WordTrace tailWord_4974253 prefixEnd_4974253 851394228689743981987111 := by
  unfold tailWord_4974253
  simp only [CollatzResearch.WordTrace]
  refine ⟨181425911648138390622591413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120950607765425593748394275 181425911648138390622591413)
  ·
    refine ⟨17008679217012974120867945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 181425911648138390622591413 17008679217012974120867945)
    ·
      refine ⟨12756509412759730590650959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17008679217012974120867945 12756509412759730590650959)
      ·
        refine ⟨19134764119139595885976439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12756509412759730590650959 19134764119139595885976439)
        ·
          refine ⟨28702146178709393828964659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19134764119139595885976439 28702146178709393828964659)
          ·
            refine ⟨43053219268064090743446989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28702146178709393828964659 43053219268064090743446989)
            ·
              refine ⟨16144957225524034028792621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43053219268064090743446989 16144957225524034028792621)
              ·
                refine ⟨6054358959571512760797233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16144957225524034028792621 6054358959571512760797233)
                ·
                  refine ⟨4540769219678634570597925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6054358959571512760797233 4540769219678634570597925)
                  ·
                    refine ⟨851394228689743981987111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4540769219678634570597925 851394228689743981987111)
                    ·
                      rfl

theorem cell23_4974253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_4974253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4974253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4974253 prefixEnd_4974253 := by exact prefixLift 4974253
  have htrace : WordTrace (prefixWord ++ tailWord_4974253) baseStart_4974253 baseEnd_4974253 := by
    simpa [prefixWord, tailWord_4974253, baseEnd_4974253] using wordTrace_append hprefix tailTrace_4974253
  have hstable : (prefixWord ++ tailWord_4974253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4974253).length < 2 ^ (prefixWord ++ tailWord_4974253).sum := by decide
  have hdescent : baseEnd_4974253 < baseStart_4974253 := by decide
  rcases family_descends (prefixWord ++ tailWord_4974253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4974263 : List Nat := [1, 1, 3, 1, 5, 1, 3, 2, 1, 2, 3]
def baseStart_4974263 : Nat := 118140960795 + 4974263 * 2 ^ 59
def prefixEnd_4974263 : Nat := 4983230072969 + 3 ^ 40 * 4974263 * 2
def baseEnd_4974263 : Nat := 2554187820875776906836287

theorem tailTrace_4974263 : CollatzResearch.WordTrace tailWord_4974263 prefixEnd_4974263 2554187820875776906836287 := by
  unfold tailWord_4974263
  simp only [CollatzResearch.WordTrace]
  refine ⟨181426276378102162330455443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120950850918734774886970295 181426276378102162330455443)
  ·
    refine ⟨272139414567153243495683165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181426276378102162330455443 272139414567153243495683165)
    ·
      refine ⟨102052280462682466310881187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 272139414567153243495683165 102052280462682466310881187)
      ·
        refine ⟨153078420694023699466321781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102052280462682466310881187 153078420694023699466321781)
        ·
          refine ⟨14351101940064721824967667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 153078420694023699466321781 14351101940064721824967667)
          ·
            refine ⟨21526652910097082737451501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14351101940064721824967667 21526652910097082737451501)
            ·
              refine ⟨8072494841286406026544313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21526652910097082737451501 8072494841286406026544313)
              ·
                refine ⟨6054371130964804519908235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8072494841286406026544313 6054371130964804519908235)
                ·
                  refine ⟨9081556696447206779862353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6054371130964804519908235 9081556696447206779862353)
                  ·
                    refine ⟨6811167522335405084896765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9081556696447206779862353 6811167522335405084896765)
                    ·
                      refine ⟨2554187820875776906836287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6811167522335405084896765 2554187820875776906836287)
                      ·
                        rfl

theorem cell23_4974263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 2, 1, 2, 3].length) (baseStart_4974263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4974263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4974263 prefixEnd_4974263 := by exact prefixLift 4974263
  have htrace : WordTrace (prefixWord ++ tailWord_4974263) baseStart_4974263 baseEnd_4974263 := by
    simpa [prefixWord, tailWord_4974263, baseEnd_4974263] using wordTrace_append hprefix tailTrace_4974263
  have hstable : (prefixWord ++ tailWord_4974263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4974263).length < 2 ^ (prefixWord ++ tailWord_4974263).sum := by decide
  have hdescent : baseEnd_4974263 < baseStart_4974263 := by decide
  rcases family_descends (prefixWord ++ tailWord_4974263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4974274 : List Nat := [3, 5, 1, 2, 1, 1, 3, 1, 1, 5]
def baseStart_4974274 : Nat := 118140960795 + 4974274 * 2 ^ 59
def prefixEnd_4974274 : Nat := 4983230072969 + 3 ^ 40 * 4974274 * 2
def baseEnd_4974274 : Nat := 851397823054325454599579

theorem tailTrace_4974274 : CollatzResearch.WordTrace tailWord_4974274 prefixEnd_4974274 851397823054325454599579 := by
  unfold tailWord_4974274
  simp only [CollatzResearch.WordTrace]
  refine ⟨45356669395265577802276469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120951118387374874139403917 45356669395265577802276469)
  ·
    refine ⟨4252187755806147918963419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45356669395265577802276469 4252187755806147918963419)
    ·
      refine ⟨6378281633709221878445129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4252187755806147918963419 6378281633709221878445129)
      ·
        refine ⟨4783711225281916408833847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6378281633709221878445129 4783711225281916408833847)
        ·
          refine ⟨7175566837922874613250771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4783711225281916408833847 7175566837922874613250771)
          ·
            refine ⟨10763350256884311919876157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7175566837922874613250771 10763350256884311919876157)
            ·
              refine ⟨4036256346331616969953559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10763350256884311919876157 4036256346331616969953559)
              ·
                refine ⟨6054384519497425454930339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4036256346331616969953559 6054384519497425454930339)
                ·
                  refine ⟨9081576779246138182395509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6054384519497425454930339 9081576779246138182395509)
                  ·
                    refine ⟨851397823054325454599579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9081576779246138182395509 851397823054325454599579)
                    ·
                      rfl

theorem cell23_4974274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_4974274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4974274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4974274 prefixEnd_4974274 := by exact prefixLift 4974274
  have htrace : WordTrace (prefixWord ++ tailWord_4974274) baseStart_4974274 baseEnd_4974274 := by
    simpa [prefixWord, tailWord_4974274, baseEnd_4974274] using wordTrace_append hprefix tailTrace_4974274
  have hstable : (prefixWord ++ tailWord_4974274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4974274).length < 2 ^ (prefixWord ++ tailWord_4974274).sum := by decide
  have hdescent : baseEnd_4974274 < baseStart_4974274 := by decide
  rcases family_descends (prefixWord ++ tailWord_4974274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4974300 : List Nat := [2, 2, 5, 1, 3, 1, 1, 8]
def baseStart_4974300 : Nat := 118140960795 + 4974300 * 2 ^ 59
def prefixEnd_4974300 : Nat := 4983230072969 + 3 ^ 40 * 4974300 * 2
def baseEnd_4974300 : Nat := 94600252579999750447171

theorem tailTrace_4974300 : CollatzResearch.WordTrace tailWord_4974300 prefixEnd_4974300 94600252579999750447171 := by
  unfold tailWord_4974300
  simp only [CollatzResearch.WordTrace]
  refine ⟨90713812939484058824776177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120951750585978745099701569 90713812939484058824776177)
  ·
    refine ⟨68035359704613044118582133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90713812939484058824776177 68035359704613044118582133)
    ·
      refine ⟨6378314972307472886117075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 68035359704613044118582133 6378314972307472886117075)
      ·
        refine ⟨9567472458461209329175613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6378314972307472886117075 9567472458461209329175613)
        ·
          refine ⟨3587802171922953498440855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9567472458461209329175613 3587802171922953498440855)
          ·
            refine ⟨5381703257884430247661283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3587802171922953498440855 5381703257884430247661283)
            ·
              refine ⟨8072554886826645371491925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5381703257884430247661283 8072554886826645371491925)
              ·
                refine ⟨94600252579999750447171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8072554886826645371491925 94600252579999750447171)
                ·
                  rfl

theorem cell23_4974300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 8].length) (baseStart_4974300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4974300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4974300 prefixEnd_4974300 := by exact prefixLift 4974300
  have htrace : WordTrace (prefixWord ++ tailWord_4974300) baseStart_4974300 baseEnd_4974300 := by
    simpa [prefixWord, tailWord_4974300, baseEnd_4974300] using wordTrace_append hprefix tailTrace_4974300
  have hstable : (prefixWord ++ tailWord_4974300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4974300).length < 2 ^ (prefixWord ++ tailWord_4974300).sum := by decide
  have hdescent : baseEnd_4974300 < baseStart_4974300 := by decide
  rcases family_descends (prefixWord ++ tailWord_4974300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4974346 : List Nat := [3, 1, 2, 2, 1, 3, 1, 2, 2, 2, 4]
def baseStart_4974346 : Nat := 118140960795 + 4974346 * 2 ^ 59
def prefixEnd_4974346 : Nat := 4983230072969 + 3 ^ 40 * 4974346 * 2
def baseEnd_4974346 : Nat := 2554230439770100082098405

theorem tailTrace_4974346 : CollatzResearch.WordTrace tailWord_4974346 prefixEnd_4974346 2554230439770100082098405 := by
  unfold tailWord_4974346
  simp only [CollatzResearch.WordTrace]
  refine ⟨45357325909200366876431723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120952869091200978337151261 45357325909200366876431723)
  ·
    refine ⟨68035988863800550314647585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45357325909200366876431723 68035988863800550314647585)
    ·
      refine ⟨51026991647850412735985689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68035988863800550314647585 51026991647850412735985689)
      ·
        refine ⟨38270243735887809551989267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51026991647850412735985689 38270243735887809551989267)
        ·
          refine ⟨57405365603831714327983901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38270243735887809551989267 57405365603831714327983901)
          ·
            refine ⟨21527012101436892872993963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57405365603831714327983901 21527012101436892872993963)
            ·
              refine ⟨32290518152155339309490945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21527012101436892872993963 32290518152155339309490945)
              ·
                refine ⟨24217888614116504482118209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32290518152155339309490945 24217888614116504482118209)
                ·
                  refine ⟨18163416460587378361588657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24217888614116504482118209 18163416460587378361588657)
                  ·
                    refine ⟨13622562345440533771191493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18163416460587378361588657 13622562345440533771191493)
                    ·
                      refine ⟨2554230439770100082098405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13622562345440533771191493 2554230439770100082098405)
                      ·
                        rfl

theorem cell23_4974346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_4974346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4974346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4974346 prefixEnd_4974346 := by exact prefixLift 4974346
  have htrace : WordTrace (prefixWord ++ tailWord_4974346) baseStart_4974346 baseEnd_4974346 := by
    simpa [prefixWord, tailWord_4974346, baseEnd_4974346] using wordTrace_append hprefix tailTrace_4974346
  have hstable : (prefixWord ++ tailWord_4974346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4974346).length < 2 ^ (prefixWord ++ tailWord_4974346).sum := by decide
  have hdescent : baseEnd_4974346 < baseStart_4974346 := by decide
  rcases family_descends (prefixWord ++ tailWord_4974346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4974367 : List Nat := [1, 1, 2, 4, 2, 1, 5, 1, 2, 2, 2]
def baseStart_4974367 : Nat := 118140960795 + 4974367 * 2 ^ 59
def prefixEnd_4974367 : Nat := 4983230072969 + 3 ^ 40 * 4974367 * 2
def baseEnd_4974367 : Nat := 2554241222863844499935809

theorem tailTrace_4974367 : CollatzResearch.WordTrace tailWord_4974367 prefixEnd_4974367 2554241222863844499935809 := by
  unfold tailWord_4974367
  simp only [CollatzResearch.WordTrace]
  refine ⟨181430069569725388092241355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120953379713150258728160903 181430069569725388092241355)
  ·
    refine ⟨272145104354588082138362033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181430069569725388092241355 272145104354588082138362033)
    ·
      refine ⟨204108828265941061603771525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 272145104354588082138362033 204108828265941061603771525)
      ·
        refine ⟨38270405299863949050707161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 204108828265941061603771525 38270405299863949050707161)
        ·
          refine ⟨28702803974897961788030371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38270405299863949050707161 28702803974897961788030371)
          ·
            refine ⟨43054205962346942682045557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28702803974897961788030371 43054205962346942682045557)
            ·
              refine ⟨4036331808970025876441771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43054205962346942682045557 4036331808970025876441771)
              ·
                refine ⟨6054497713455038814662657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4036331808970025876441771 6054497713455038814662657)
                ·
                  refine ⟨4540873285091279110996993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6054497713455038814662657 4540873285091279110996993)
                  ·
                    refine ⟨3405654963818459333247745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4540873285091279110996993 3405654963818459333247745)
                    ·
                      refine ⟨2554241222863844499935809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3405654963818459333247745 2554241222863844499935809)
                      ·
                        rfl

theorem cell23_4974367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 5, 1, 2, 2, 2].length) (baseStart_4974367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4974367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4974367 prefixEnd_4974367 := by exact prefixLift 4974367
  have htrace : WordTrace (prefixWord ++ tailWord_4974367) baseStart_4974367 baseEnd_4974367 := by
    simpa [prefixWord, tailWord_4974367, baseEnd_4974367] using wordTrace_append hprefix tailTrace_4974367
  have hstable : (prefixWord ++ tailWord_4974367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4974367).length < 2 ^ (prefixWord ++ tailWord_4974367).sum := by decide
  have hdescent : baseEnd_4974367 < baseStart_4974367 := by decide
  rcases family_descends (prefixWord ++ tailWord_4974367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4974386 : List Nat := [3, 2, 1, 1, 3, 2, 2, 1, 1, 7]
def baseStart_4974386 : Nat := 118140960795 + 4974386 * 2 ^ 59
def prefixEnd_4974386 : Nat := 4983230072969 + 3 ^ 40 * 4974386 * 2
def baseEnd_4974386 : Nat := 851416992998759975199407

theorem tailTrace_4974386 : CollatzResearch.WordTrace tailWord_4974386 prefixEnd_4974386 851416992998759975199407 := by
  unfold tailWord_4974386
  simp only [CollatzResearch.WordTrace]
  refine ⟨45357690639164138584295753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120953841704437702891455341 45357690639164138584295753)
  ·
    refine ⟨34018267979373103938221815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45357690639164138584295753 34018267979373103938221815)
    ·
      refine ⟨51027401969059655907332723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34018267979373103938221815 51027401969059655907332723)
      ·
        refine ⟨76541102953589483860999085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51027401969059655907332723 76541102953589483860999085)
        ·
          refine ⟨28702913607596056447874657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76541102953589483860999085 28702913607596056447874657)
          ·
            refine ⟨21527185205697042335905993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28702913607596056447874657 21527185205697042335905993)
            ·
              refine ⟨16145388904272781751929495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21527185205697042335905993 16145388904272781751929495)
              ·
                refine ⟨24218083356409172627894243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16145388904272781751929495 24218083356409172627894243)
                ·
                  refine ⟨36327125034613758941841365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24218083356409172627894243 36327125034613758941841365)
                  ·
                    refine ⟨851416992998759975199407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36327125034613758941841365 851416992998759975199407)
                    ·
                      rfl

theorem cell23_4974386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 1, 7].length) (baseStart_4974386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4974386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4974386 prefixEnd_4974386 := by exact prefixLift 4974386
  have htrace : WordTrace (prefixWord ++ tailWord_4974386) baseStart_4974386 baseEnd_4974386 := by
    simpa [prefixWord, tailWord_4974386, baseEnd_4974386] using wordTrace_append hprefix tailTrace_4974386
  have hstable : (prefixWord ++ tailWord_4974386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4974386).length < 2 ^ (prefixWord ++ tailWord_4974386).sum := by decide
  have hdescent : baseEnd_4974386 < baseStart_4974386 := by decide
  rcases family_descends (prefixWord ++ tailWord_4974386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4974413 : List Nat := [1, 6, 1, 2, 1, 1, 1, 1, 1, 1, 7]
def baseStart_4974413 : Nat := 118140960795 + 4974413 * 2 ^ 59
def prefixEnd_4974413 : Nat := 4983230072969 + 3 ^ 40 * 4974413 * 2
def baseEnd_4974413 : Nat := 2554264842973951319960597

theorem tailTrace_4974413 : CollatzResearch.WordTrace tailWord_4974413 prefixEnd_4974413 2554264842973951319960597 := by
  unfold tailWord_4974413
  simp only [CollatzResearch.WordTrace]
  refine ⟨181431747327558737948415893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120954498218372491965610595 181431747327558737948415893)
  ·
    refine ⟨8504613155979315841331995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 181431747327558737948415893 8504613155979315841331995)
    ·
      refine ⟨12756919733968973761997993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8504613155979315841331995 12756919733968973761997993)
      ·
        refine ⟨9567689800476730321498495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12756919733968973761997993 9567689800476730321498495)
        ·
          refine ⟨14351534700715095482247743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9567689800476730321498495 14351534700715095482247743)
          ·
            refine ⟨21527302051072643223371615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14351534700715095482247743 21527302051072643223371615)
            ·
              refine ⟨32290953076608964835057423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21527302051072643223371615 32290953076608964835057423)
              ·
                refine ⟨48436429614913447252586135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32290953076608964835057423 48436429614913447252586135)
                ·
                  refine ⟨72654644422370170878879203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48436429614913447252586135 72654644422370170878879203)
                  ·
                    refine ⟨108981966633555256318318805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 72654644422370170878879203 108981966633555256318318805)
                    ·
                      refine ⟨2554264842973951319960597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 108981966633555256318318805 2554264842973951319960597)
                      ·
                        rfl

theorem cell23_4974413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_4974413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4974413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4974413 prefixEnd_4974413 := by exact prefixLift 4974413
  have htrace : WordTrace (prefixWord ++ tailWord_4974413) baseStart_4974413 baseEnd_4974413 := by
    simpa [prefixWord, tailWord_4974413, baseEnd_4974413] using wordTrace_append hprefix tailTrace_4974413
  have hstable : (prefixWord ++ tailWord_4974413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4974413).length < 2 ^ (prefixWord ++ tailWord_4974413).sum := by decide
  have hdescent : baseEnd_4974413 < baseStart_4974413 := by decide
  rcases family_descends (prefixWord ++ tailWord_4974413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4974450 : List Nat := [3, 2, 1, 2, 1, 1, 1, 7, 1, 4]
def baseStart_4974450 : Nat := 118140960795 + 4974450 * 2 ^ 59
def prefixEnd_4974450 : Nat := 4983230072969 + 3 ^ 40 * 4974450 * 2
def baseEnd_4974450 : Nat := 851427947252722558399309

theorem tailTrace_4974450 : CollatzResearch.WordTrace tailWord_4974450 prefixEnd_4974450 851427947252722558399309 := by
  unfold tailWord_4974450
  simp only [CollatzResearch.WordTrace]
  refine ⟨45358274207106173316878201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120955397885616462178341869 45358274207106173316878201)
  ·
    refine ⟨34018705655329629987658651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45358274207106173316878201 34018705655329629987658651)
    ·
      refine ⟨51028058482994444981487977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34018705655329629987658651 51028058482994444981487977)
      ·
        refine ⟨38271043862245833736115983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51028058482994444981487977 38271043862245833736115983)
        ·
          refine ⟨57406565793368750604173975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38271043862245833736115983 57406565793368750604173975)
          ·
            refine ⟨86109848690053125906260963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57406565793368750604173975 86109848690053125906260963)
            ·
              refine ⟨129164773035079688859391445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86109848690053125906260963 129164773035079688859391445)
              ·
                refine ⟨3027299368009680207641987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 129164773035079688859391445 3027299368009680207641987)
                ·
                  refine ⟨4540949052014520311462981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3027299368009680207641987 4540949052014520311462981)
                  ·
                    refine ⟨851427947252722558399309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4540949052014520311462981 851427947252722558399309)
                    ·
                      rfl

theorem cell23_4974450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 7, 1, 4].length) (baseStart_4974450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4974450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4974450 prefixEnd_4974450 := by exact prefixLift 4974450
  have htrace : WordTrace (prefixWord ++ tailWord_4974450) baseStart_4974450 baseEnd_4974450 := by
    simpa [prefixWord, tailWord_4974450, baseEnd_4974450] using wordTrace_append hprefix tailTrace_4974450
  have hstable : (prefixWord ++ tailWord_4974450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4974450).length < 2 ^ (prefixWord ++ tailWord_4974450).sum := by decide
  have hdescent : baseEnd_4974450 < baseStart_4974450 := by decide
  rcases family_descends (prefixWord ++ tailWord_4974450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4974456 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 4, 5, 3]
def baseStart_4974456 : Nat := 118140960795 + 4974456 * 2 ^ 59
def prefixEnd_4974456 : Nat := 4983230072969 + 3 ^ 40 * 4974456 * 2
def baseEnd_4974456 : Nat := 2554286922642094651722899

theorem tailTrace_4974456 : CollatzResearch.WordTrace tailWord_4974456 prefixEnd_4974456 2554286922642094651722899 := by
  unfold tailWord_4974456
  simp only [CollatzResearch.WordTrace]
  refine ⟨90716657833201478146115611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120955543777601970861487481 90716657833201478146115611)
  ·
    refine ⟨136074986749802217219173417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90716657833201478146115611 136074986749802217219173417)
    ·
      refine ⟨102056240062351662914380063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136074986749802217219173417 102056240062351662914380063)
      ·
        refine ⟨153084360093527494371570095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102056240062351662914380063 153084360093527494371570095)
        ·
          refine ⟨229626540140291241557355143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153084360093527494371570095 229626540140291241557355143)
          ·
            refine ⟨344439810210436862336032715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229626540140291241557355143 344439810210436862336032715)
            ·
              refine ⟨516659715315655293504049073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 344439810210436862336032715 516659715315655293504049073)
              ·
                refine ⟨387494786486741470128036805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 516659715315655293504049073 387494786486741470128036805)
                ·
                  refine ⟨72655272466264025649006901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 387494786486741470128036805 72655272466264025649006901)
                  ·
                    refine ⟨6811431793712252404594397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 72655272466264025649006901 6811431793712252404594397)
                    ·
                      refine ⟨2554286922642094651722899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6811431793712252404594397 2554286922642094651722899)
                      ·
                        rfl

theorem cell23_4974456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 4, 5, 3].length) (baseStart_4974456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4974456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4974456 prefixEnd_4974456 := by exact prefixLift 4974456
  have htrace : WordTrace (prefixWord ++ tailWord_4974456) baseStart_4974456 baseEnd_4974456 := by
    simpa [prefixWord, tailWord_4974456, baseEnd_4974456] using wordTrace_append hprefix tailTrace_4974456
  have hstable : (prefixWord ++ tailWord_4974456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4974456).length < 2 ^ (prefixWord ++ tailWord_4974456).sum := by decide
  have hdescent : baseEnd_4974456 < baseStart_4974456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4974456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4974467 : List Nat := [1, 1, 1, 3, 4, 2, 4, 2, 1, 4]
def baseStart_4974467 : Nat := 118140960795 + 4974467 * 2 ^ 59
def prefixEnd_4974467 : Nat := 4983230072969 + 3 ^ 40 * 4974467 * 2
def baseEnd_4974467 : Nat := 851430856976431369561783

theorem tailTrace_4974467 : CollatzResearch.WordTrace tailWord_4974467 prefixEnd_4974467 851430856976431369561783 := by
  unfold tailWord_4974467
  simp only [CollatzResearch.WordTrace]
  refine ⟨181433716869363105170881655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120955811246242070113921103 181433716869363105170881655)
  ·
    refine ⟨272150575304044657756322483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181433716869363105170881655 272150575304044657756322483)
    ·
      refine ⟨408225862956066986634483725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272150575304044657756322483 408225862956066986634483725)
      ·
        refine ⟨153084698608525119987931397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 408225862956066986634483725 153084698608525119987931397)
        ·
          refine ⟨28703380989098459997737137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 153084698608525119987931397 28703380989098459997737137)
          ·
            refine ⟨21527535741823844998302853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28703380989098459997737137 21527535741823844998302853)
            ·
              refine ⟨4036412951591970937181785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21527535741823844998302853 4036412951591970937181785)
              ·
                refine ⟨3027309713693978202886339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4036412951591970937181785 3027309713693978202886339)
                ·
                  refine ⟨4540964570540967304329509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3027309713693978202886339 4540964570540967304329509)
                  ·
                    refine ⟨851430856976431369561783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4540964570540967304329509 851430856976431369561783)
                    ·
                      rfl

theorem cell23_4974467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 4, 2, 1, 4].length) (baseStart_4974467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4974467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4974467 prefixEnd_4974467 := by exact prefixLift 4974467
  have htrace : WordTrace (prefixWord ++ tailWord_4974467) baseStart_4974467 baseEnd_4974467 := by
    simpa [prefixWord, tailWord_4974467, baseEnd_4974467] using wordTrace_append hprefix tailTrace_4974467
  have hstable : (prefixWord ++ tailWord_4974467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4974467).length < 2 ^ (prefixWord ++ tailWord_4974467).sum := by decide
  have hdescent : baseEnd_4974467 < baseStart_4974467 := by decide
  rcases family_descends (prefixWord ++ tailWord_4974467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4974490 : List Nat := [3, 1, 1, 4, 2, 1, 1, 1, 5, 1, 3]
def baseStart_4974490 : Nat := 118140960795 + 4974490 * 2 ^ 59
def prefixEnd_4974490 : Nat := 4983230072969 + 3 ^ 40 * 4974490 * 2
def baseEnd_4974490 : Nat := 2554304380984347518697743

theorem tailTrace_4974490 : CollatzResearch.WordTrace tailWord_4974490 prefixEnd_4974490 2554304380984347518697743 := by
  unfold tailWord_4974490
  simp only [CollatzResearch.WordTrace]
  refine ⟨45358638937069945024742231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120956370498853186732645949 45358638937069945024742231)
  ·
    refine ⟨68037958405604917537113347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45358638937069945024742231 68037958405604917537113347)
    ·
      refine ⟨102056937608407376305670021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68037958405604917537113347 102056937608407376305670021)
      ·
        refine ⟨19135675801576383057313129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102056937608407376305670021 19135675801576383057313129)
        ·
          refine ⟨14351756851182287292984847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19135675801576383057313129 14351756851182287292984847)
          ·
            refine ⟨21527635276773430939477271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14351756851182287292984847 21527635276773430939477271)
            ·
              refine ⟨32291452915160146409215907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21527635276773430939477271 32291452915160146409215907)
              ·
                refine ⟨48437179372740219613823861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32291452915160146409215907 48437179372740219613823861)
                ·
                  refine ⟨4540985566194395588795987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48437179372740219613823861 4540985566194395588795987)
                  ·
                    refine ⟨6811478349291593383193981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4540985566194395588795987 6811478349291593383193981)
                    ·
                      refine ⟨2554304380984347518697743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6811478349291593383193981 2554304380984347518697743)
                      ·
                        rfl

theorem cell23_4974490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_4974490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4974490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4974490 prefixEnd_4974490 := by exact prefixLift 4974490
  have htrace : WordTrace (prefixWord ++ tailWord_4974490) baseStart_4974490 baseEnd_4974490 := by
    simpa [prefixWord, tailWord_4974490, baseEnd_4974490] using wordTrace_append hprefix tailTrace_4974490
  have hstable : (prefixWord ++ tailWord_4974490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4974490).length < 2 ^ (prefixWord ++ tailWord_4974490).sum := by decide
  have hdescent : baseEnd_4974490 < baseStart_4974490 := by decide
  rcases family_descends (prefixWord ++ tailWord_4974490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4974493 : List Nat := [1, 4, 2, 1, 2, 2, 2, 1, 3, 5]
def baseStart_4974493 : Nat := 118140960795 + 4974493 * 2 ^ 59
def prefixEnd_4974493 : Nat := 4983230072969 + 3 ^ 40 * 4974493 * 2
def baseEnd_4974493 : Nat := 851435307142103668986743

theorem tailTrace_4974493 : CollatzResearch.WordTrace tailWord_4974493 prefixEnd_4974493 851435307142103668986743 := by
  unfold tailWord_4974493
  simp only [CollatzResearch.WordTrace]
  refine ⟨181434665167268911611328133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120956443444845941074218755 181434665167268911611328133)
  ·
    refine ⟨34018999718862920927124025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 181434665167268911611328133 34018999718862920927124025)
    ·
      refine ⟨25514249789147190695343019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34018999718862920927124025 25514249789147190695343019)
      ·
        refine ⟨38271374683720786043014529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25514249789147190695343019 38271374683720786043014529)
        ·
          refine ⟨28703531012790589532260897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38271374683720786043014529 28703531012790589532260897)
          ·
            refine ⟨21527648259592942149195673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28703531012790589532260897 21527648259592942149195673)
            ·
              refine ⟨16145736194694706611896755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21527648259592942149195673 16145736194694706611896755)
              ·
                refine ⟨24218604292042059917845133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16145736194694706611896755 24218604292042059917845133)
                ·
                  refine ⟨9081976609515772469191925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24218604292042059917845133 9081976609515772469191925)
                  ·
                    refine ⟨851435307142103668986743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9081976609515772469191925 851435307142103668986743)
                    ·
                      rfl

theorem cell23_4974493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_4974493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4974493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4974493 prefixEnd_4974493 := by exact prefixLift 4974493
  have htrace : WordTrace (prefixWord ++ tailWord_4974493) baseStart_4974493 baseEnd_4974493 := by
    simpa [prefixWord, tailWord_4974493, baseEnd_4974493] using wordTrace_append hprefix tailTrace_4974493
  have hstable : (prefixWord ++ tailWord_4974493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4974493).length < 2 ^ (prefixWord ++ tailWord_4974493).sum := by decide
  have hdescent : baseEnd_4974493 < baseStart_4974493 := by decide
  rcases family_descends (prefixWord ++ tailWord_4974493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4974500 : List Nat := [2, 3, 1, 2, 1, 4, 1, 1, 1, 5, 2]
def baseStart_4974500 : Nat := 118140960795 + 4974500 * 2 ^ 59
def prefixEnd_4974500 : Nat := 4983230072969 + 3 ^ 40 * 4974500 * 2
def baseEnd_4974500 : Nat := 2554309515790892479572697

theorem tailTrace_4974500 : CollatzResearch.WordTrace tailWord_4974500 prefixEnd_4974500 2554309515790892479572697 := by
  unfold tailWord_4974500
  simp only [CollatzResearch.WordTrace]
  refine ⟨90717460239121775903416477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120956613652162367871221969 90717460239121775903416477)
  ·
    refine ⟨34019047589670665963781179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90717460239121775903416477 34019047589670665963781179)
    ·
      refine ⟨51028571384505998945671769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34019047589670665963781179 51028571384505998945671769)
      ·
        refine ⟨38271428538379499209253827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51028571384505998945671769 38271428538379499209253827)
        ·
          refine ⟨57407142807569248813880741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38271428538379499209253827 57407142807569248813880741)
          ·
            refine ⟨10763839276419234152602639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57407142807569248813880741 10763839276419234152602639)
            ·
              refine ⟨16145758914628851228903959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10763839276419234152602639 16145758914628851228903959)
              ·
                refine ⟨24218638371943276843355939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16145758914628851228903959 24218638371943276843355939)
                ·
                  refine ⟨36327957557914915265033909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24218638371943276843355939 36327957557914915265033909)
                  ·
                    refine ⟨3405746021054523306096929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36327957557914915265033909 3405746021054523306096929)
                    ·
                      refine ⟨2554309515790892479572697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3405746021054523306096929 2554309515790892479572697)
                      ·
                        rfl

theorem cell23_4974500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 1, 5, 2].length) (baseStart_4974500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4974500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4974500 prefixEnd_4974500 := by exact prefixLift 4974500
  have htrace : WordTrace (prefixWord ++ tailWord_4974500) baseStart_4974500 baseEnd_4974500 := by
    simpa [prefixWord, tailWord_4974500, baseEnd_4974500] using wordTrace_append hprefix tailTrace_4974500
  have hstable : (prefixWord ++ tailWord_4974500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4974500).length < 2 ^ (prefixWord ++ tailWord_4974500).sum := by decide
  have hdescent : baseEnd_4974500 < baseStart_4974500 := by decide
  rcases family_descends (prefixWord ++ tailWord_4974500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4974524 : List Nat := [2, 2, 2, 5, 1, 1, 2, 1, 3, 1, 3]
def baseStart_4974524 : Nat := 118140960795 + 4974524 * 2 ^ 59
def prefixEnd_4974524 : Nat := 4983230072969 + 3 ^ 40 * 4974524 * 2
def baseEnd_4974524 : Nat := 2554321839326600385672587

theorem tailTrace_4974524 : CollatzResearch.WordTrace tailWord_4974524 prefixEnd_4974524 2554321839326600385672587 := by
  unfold tailWord_4974524
  simp only [CollatzResearch.WordTrace]
  refine ⟨90717897915078301952853313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120957197220104402603804417 90717897915078301952853313)
  ·
    refine ⟨68038423436308726464639985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90717897915078301952853313 68038423436308726464639985)
    ·
      refine ⟨51028817577231544848479989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68038423436308726464639985 51028817577231544848479989)
      ·
        refine ⟨4783951647865457329544999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51028817577231544848479989 4783951647865457329544999)
        ·
          refine ⟨7175927471798185994317499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4783951647865457329544999 7175927471798185994317499)
          ·
            refine ⟨10763891207697278991476249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7175927471798185994317499 10763891207697278991476249)
            ·
              refine ⟨8072918405772959243607187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10763891207697278991476249 8072918405772959243607187)
              ·
                refine ⟨12109377608659438865410781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8072918405772959243607187 12109377608659438865410781)
                ·
                  refine ⟨4541016603247289574529043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12109377608659438865410781 4541016603247289574529043)
                  ·
                    refine ⟨6811524904870934361793565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4541016603247289574529043 6811524904870934361793565)
                    ·
                      refine ⟨2554321839326600385672587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6811524904870934361793565 2554321839326600385672587)
                      ·
                        rfl

theorem cell23_4974524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_4974524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4974524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4974524 prefixEnd_4974524 := by exact prefixLift 4974524
  have htrace : WordTrace (prefixWord ++ tailWord_4974524) baseStart_4974524 baseEnd_4974524 := by
    simpa [prefixWord, tailWord_4974524, baseEnd_4974524] using wordTrace_append hprefix tailTrace_4974524
  have hstable : (prefixWord ++ tailWord_4974524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4974524).length < 2 ^ (prefixWord ++ tailWord_4974524).sum := by decide
  have hdescent : baseEnd_4974524 < baseStart_4974524 := by decide
  rcases family_descends (prefixWord ++ tailWord_4974524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4974533 : List Nat := [1, 3, 1, 1, 1, 1, 1, 6, 3, 2, 3]
def baseStart_4974533 : Nat := 118140960795 + 4974533 * 2 ^ 59
def prefixEnd_4974533 : Nat := 4983230072969 + 3 ^ 40 * 4974533 * 2
def baseEnd_4974533 : Nat := 2554326460652490850460045

theorem tailTrace_4974533 : CollatzResearch.WordTrace tailWord_4974533 prefixEnd_4974533 2554326460652490850460045 := by
  unfold tailWord_4974533
  simp only [CollatzResearch.WordTrace]
  refine ⟨181436124087123998442784253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120957416058082665628522835 181436124087123998442784253)
  ·
    refine ⟨68038546532671499416044095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181436124087123998442784253 68038546532671499416044095)
    ·
      refine ⟨102057819799007249124066143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68038546532671499416044095 102057819799007249124066143)
      ·
        refine ⟨153086729698510873686099215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102057819799007249124066143 153086729698510873686099215)
        ·
          refine ⟨229630094547766310529148823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153086729698510873686099215 229630094547766310529148823)
          ·
            refine ⟨344445141821649465793723235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229630094547766310529148823 344445141821649465793723235)
            ·
              refine ⟨516667712732474198690584853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 344445141821649465793723235 516667712732474198690584853)
              ·
                refine ⟨24218799034334728063621165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 516667712732474198690584853 24218799034334728063621165)
                ·
                  refine ⟨9082049637875523023857937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24218799034334728063621165 9082049637875523023857937)
                  ·
                    refine ⟨6811537228406642267893453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9082049637875523023857937 6811537228406642267893453)
                    ·
                      refine ⟨2554326460652490850460045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6811537228406642267893453 2554326460652490850460045)
                      ·
                        rfl

theorem cell23_4974533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 3, 2, 3].length) (baseStart_4974533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4974533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4974533 prefixEnd_4974533 := by exact prefixLift 4974533
  have htrace : WordTrace (prefixWord ++ tailWord_4974533) baseStart_4974533 baseEnd_4974533 := by
    simpa [prefixWord, tailWord_4974533, baseEnd_4974533] using wordTrace_append hprefix tailTrace_4974533
  have hstable : (prefixWord ++ tailWord_4974533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4974533).length < 2 ^ (prefixWord ++ tailWord_4974533).sum := by decide
  have hdescent : baseEnd_4974533 < baseStart_4974533 := by decide
  rcases family_descends (prefixWord ++ tailWord_4974533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4974540 : List Nat := [2, 2, 1, 4, 1, 4, 1, 1, 1, 6]
def baseStart_4974540 : Nat := 118140960795 + 4974540 * 2 ^ 59
def prefixEnd_4974540 : Nat := 4983230072969 + 3 ^ 40 * 4974540 * 2
def baseEnd_4974540 : Nat := 851443351672357441024171

theorem tailTrace_4974540 : CollatzResearch.WordTrace tailWord_4974540 prefixEnd_4974540 851443351672357441024171 := by
  unfold tailWord_4974540
  simp only [CollatzResearch.WordTrace]
  refine ⟨90718189699049319319144537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120957586265399092425526049 90718189699049319319144537)
  ·
    refine ⟨68038642274286989489358403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90718189699049319319144537 68038642274286989489358403)
    ·
      refine ⟨102057963411430484234037605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68038642274286989489358403 102057963411430484234037605)
      ·
        refine ⟨19135868139643215793882051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102057963411430484234037605 19135868139643215793882051)
        ·
          refine ⟨28703802209464823690823077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19135868139643215793882051 28703802209464823690823077)
          ·
            refine ⟨5381962914274654442029327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28703802209464823690823077 5381962914274654442029327)
            ·
              refine ⟨8072944371411981663043991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5381962914274654442029327 8072944371411981663043991)
              ·
                refine ⟨12109416557117972494565987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8072944371411981663043991 12109416557117972494565987)
                ·
                  refine ⟨18164124835676958741848981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12109416557117972494565987 18164124835676958741848981)
                  ·
                    refine ⟨851443351672357441024171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18164124835676958741848981 851443351672357441024171)
                    ·
                      rfl

theorem cell23_4974540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 1, 1, 6].length) (baseStart_4974540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4974540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4974540 prefixEnd_4974540 := by exact prefixLift 4974540
  have htrace : WordTrace (prefixWord ++ tailWord_4974540) baseStart_4974540 baseEnd_4974540 := by
    simpa [prefixWord, tailWord_4974540, baseEnd_4974540] using wordTrace_append hprefix tailTrace_4974540
  have hstable : (prefixWord ++ tailWord_4974540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4974540).length < 2 ^ (prefixWord ++ tailWord_4974540).sum := by decide
  have hdescent : baseEnd_4974540 < baseStart_4974540 := by decide
  rcases family_descends (prefixWord ++ tailWord_4974540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4974553 : List Nat := [1, 2, 1, 2, 6, 1, 1, 9]
def baseStart_4974553 : Nat := 118140960795 + 4974553 * 2 ^ 59
def prefixEnd_4974553 : Nat := 4983230072969 + 3 ^ 40 * 4974553 * 2
def baseEnd_4974553 : Nat := 94605064083910398970739

theorem tailTrace_4974553 : CollatzResearch.WordTrace tailWord_4974553 prefixEnd_4974553 94605064083910398970739 := by
  unfold tailWord_4974553
  simp only [CollatzResearch.WordTrace]
  refine ⟨181436853547051541858512313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120957902364701027905674875 181436853547051541858512313)
  ·
    refine ⟨136077640160288656393884235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181436853547051541858512313 136077640160288656393884235)
    ·
      refine ⟨204116460240432984590826353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136077640160288656393884235 204116460240432984590826353)
      ·
        refine ⟨153087345180324738443119765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204116460240432984590826353 153087345180324738443119765)
        ·
          refine ⟨7175969305327722114521239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 153087345180324738443119765 7175969305327722114521239)
          ·
            refine ⟨10763953957991583171781859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7175969305327722114521239 10763953957991583171781859)
            ·
              refine ⟨16145930936987374757672789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10763953957991583171781859 16145930936987374757672789)
              ·
                refine ⟨94605064083910398970739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16145930936987374757672789 94605064083910398970739)
                ·
                  rfl

theorem cell23_4974553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 9].length) (baseStart_4974553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4974553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4974553 prefixEnd_4974553 := by exact prefixLift 4974553
  have htrace : WordTrace (prefixWord ++ tailWord_4974553) baseStart_4974553 baseEnd_4974553 := by
    simpa [prefixWord, tailWord_4974553, baseEnd_4974553] using wordTrace_append hprefix tailTrace_4974553
  have hstable : (prefixWord ++ tailWord_4974553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4974553).length < 2 ^ (prefixWord ++ tailWord_4974553).sum := by decide
  have hdescent : baseEnd_4974553 < baseStart_4974553 := by decide
  rcases family_descends (prefixWord ++ tailWord_4974553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4974597 : List Nat := [1, 3, 1, 1, 2, 5, 1, 3, 2, 1, 3]
def baseStart_4974597 : Nat := 118140960795 + 4974597 * 2 ^ 59
def prefixEnd_4974597 : Nat := 4983230072969 + 3 ^ 40 * 4974597 * 2
def baseEnd_4974597 : Nat := 2554359323414378600059751

theorem tailTrace_4974597 : CollatzResearch.WordTrace tailWord_4974597 prefixEnd_4974597 2554359323414378600059751 := by
  unfold tailWord_4974597
  simp only [CollatzResearch.WordTrace]
  refine ⟨181438458358892137373114045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120958972239261424915409363 181438458358892137373114045)
  ·
    refine ⟨68039421884584551514917767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181438458358892137373114045 68039421884584551514917767)
    ·
      refine ⟨102059132826876827272376651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68039421884584551514917767 102059132826876827272376651)
      ·
        refine ⟨153088699240315240908564977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102059132826876827272376651 153088699240315240908564977)
        ·
          refine ⟨114816524430236430681423733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153088699240315240908564977 114816524430236430681423733)
          ·
            refine ⟨10764049165334665376383475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 114816524430236430681423733 10764049165334665376383475)
            ·
              refine ⟨16146073748001998064575213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10764049165334665376383475 16146073748001998064575213)
              ·
                refine ⟨6054777655500749274215705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16146073748001998064575213 6054777655500749274215705)
                ·
                  refine ⟨4541083241625561955661779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6054777655500749274215705 4541083241625561955661779)
                  ·
                    refine ⟨6811624862438342933492669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4541083241625561955661779 6811624862438342933492669)
                    ·
                      refine ⟨2554359323414378600059751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6811624862438342933492669 2554359323414378600059751)
                      ·
                        rfl

theorem cell23_4974597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 3, 2, 1, 3].length) (baseStart_4974597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4974597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4974597 prefixEnd_4974597 := by exact prefixLift 4974597
  have htrace : WordTrace (prefixWord ++ tailWord_4974597) baseStart_4974597 baseEnd_4974597 := by
    simpa [prefixWord, tailWord_4974597, baseEnd_4974597] using wordTrace_append hprefix tailTrace_4974597
  have hstable : (prefixWord ++ tailWord_4974597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4974597).length < 2 ^ (prefixWord ++ tailWord_4974597).sum := by decide
  have hdescent : baseEnd_4974597 < baseStart_4974597 := by decide
  rcases family_descends (prefixWord ++ tailWord_4974597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4974623 : List Nat := [1, 1, 2, 4, 1, 2, 1, 3, 2, 1, 5]
def baseStart_4974623 : Nat := 118140960795 + 4974623 * 2 ^ 59
def prefixEnd_4974623 : Nat := 4983230072969 + 3 ^ 40 * 4974623 * 2
def baseEnd_4974623 : Nat := 2554372673911395498334631

theorem tailTrace_4974623 : CollatzResearch.WordTrace tailWord_4974623 prefixEnd_4974623 2554372673911395498334631 := by
  unfold tailWord_4974623
  simp only [CollatzResearch.WordTrace]
  refine ⟨181439406656797943813560523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120959604437865295875707015 181439406656797943813560523)
  ·
    refine ⟨272159109985196915720340785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181439406656797943813560523 272159109985196915720340785)
    ·
      refine ⟨204119332488897686790255589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 272159109985196915720340785 204119332488897686790255589)
      ·
        refine ⟨38272374841668316273172923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 204119332488897686790255589 38272374841668316273172923)
        ·
          refine ⟨57408562262502474409759385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38272374841668316273172923 57408562262502474409759385)
          ·
            refine ⟨43056421696876855807319539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57408562262502474409759385 43056421696876855807319539)
            ·
              refine ⟨64584632545315283710979309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43056421696876855807319539 64584632545315283710979309)
              ·
                refine ⟨24219237204493231391617241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64584632545315283710979309 24219237204493231391617241)
                ·
                  refine ⟨18164427903369923543712931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24219237204493231391617241 18164427903369923543712931)
                  ·
                    refine ⟨27246641855054885315569397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18164427903369923543712931 27246641855054885315569397)
                    ·
                      refine ⟨2554372673911395498334631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27246641855054885315569397 2554372673911395498334631)
                      ·
                        rfl

theorem cell23_4974623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_4974623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4974623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4974623 prefixEnd_4974623 := by exact prefixLift 4974623
  have htrace : WordTrace (prefixWord ++ tailWord_4974623) baseStart_4974623 baseEnd_4974623 := by
    simpa [prefixWord, tailWord_4974623, baseEnd_4974623] using wordTrace_append hprefix tailTrace_4974623
  have hstable : (prefixWord ++ tailWord_4974623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4974623).length < 2 ^ (prefixWord ++ tailWord_4974623).sum := by decide
  have hdescent : baseEnd_4974623 < baseStart_4974623 := by decide
  rcases family_descends (prefixWord ++ tailWord_4974623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4974631 : List Nat := [1, 1, 7, 1, 2, 1, 2, 2, 2, 1, 3]
def baseStart_4974631 : Nat := 118140960795 + 4974631 * 2 ^ 59
def prefixEnd_4974631 : Nat := 4983230072969 + 3 ^ 40 * 4974631 * 2
def baseEnd_4974631 : Nat := 2554376781756631467034595

theorem tailTrace_4974631 : CollatzResearch.WordTrace tailWord_4974631 prefixEnd_4974631 2554376781756631467034595 := by
  unfold tailWord_4974631
  simp only [CollatzResearch.WordTrace]
  refine ⟨181439698440768961179851747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120959798960512640786567831 181439698440768961179851747)
  ·
    refine ⟨272159547661153441769777621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181439698440768961179851747 272159547661153441769777621)
    ·
      refine ⟨6378739398308283791479163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 272159547661153441769777621 6378739398308283791479163)
      ·
        refine ⟨9568109097462425687218745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6378739398308283791479163 9568109097462425687218745)
        ·
          refine ⟨7176081823096819265414059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9568109097462425687218745 7176081823096819265414059)
          ·
            refine ⟨10764122734645228898121089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7176081823096819265414059 10764122734645228898121089)
            ·
              refine ⟨8073092050983921673590817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10764122734645228898121089 8073092050983921673590817)
              ·
                refine ⟨6054819038237941255193113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8073092050983921673590817 6054819038237941255193113)
                ·
                  refine ⟨4541114278678455941394835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6054819038237941255193113 4541114278678455941394835)
                  ·
                    refine ⟨6811671418017683912092253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4541114278678455941394835 6811671418017683912092253)
                    ·
                      refine ⟨2554376781756631467034595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6811671418017683912092253 2554376781756631467034595)
                      ·
                        rfl

theorem cell23_4974631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_4974631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4974631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4974631 prefixEnd_4974631 := by exact prefixLift 4974631
  have htrace : WordTrace (prefixWord ++ tailWord_4974631) baseStart_4974631 baseEnd_4974631 := by
    simpa [prefixWord, tailWord_4974631, baseEnd_4974631] using wordTrace_append hprefix tailTrace_4974631
  have hstable : (prefixWord ++ tailWord_4974631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4974631).length < 2 ^ (prefixWord ++ tailWord_4974631).sum := by decide
  have hdescent : baseEnd_4974631 < baseStart_4974631 := by decide
  rcases family_descends (prefixWord ++ tailWord_4974631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4974632 : List Nat := [2, 1, 5, 3, 2, 1, 2, 2, 1, 2, 2]
def baseStart_4974632 : Nat := 118140960795 + 4974632 * 2 ^ 59
def prefixEnd_4974632 : Nat := 4983230072969 + 3 ^ 40 * 4974632 * 2
def baseEnd_4974632 : Nat := 2554377295237285963122091

theorem tailTrace_4974632 : CollatzResearch.WordTrace tailWord_4974632 prefixEnd_4974632 2554377295237285963122091 := by
  unfold tailWord_4974632
  simp only [CollatzResearch.WordTrace]
  refine ⟨90719867456882669175319075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120959823275843558900425433 90719867456882669175319075)
  ·
    refine ⟨136079801185324003762978613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90719867456882669175319075 136079801185324003762978613)
    ·
      refine ⟨12757481361124125352779245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 136079801185324003762978613 12757481361124125352779245)
      ·
        refine ⟨4784055510421547007292217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12757481361124125352779245 4784055510421547007292217)
        ·
          refine ⟨3588041632816160255469163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4784055510421547007292217 3588041632816160255469163)
          ·
            refine ⟨5382062449224240383203745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3588041632816160255469163 5382062449224240383203745)
            ·
              refine ⟨4036546836918180287402809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5382062449224240383203745 4036546836918180287402809)
              ·
                refine ⟨3027410127688635215552107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4036546836918180287402809 3027410127688635215552107)
                ·
                  refine ⟨4541115191532952823328161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3027410127688635215552107 4541115191532952823328161)
                  ·
                    refine ⟨3405836393649714617496121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4541115191532952823328161 3405836393649714617496121)
                    ·
                      refine ⟨2554377295237285963122091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3405836393649714617496121 2554377295237285963122091)
                      ·
                        rfl

theorem cell23_4974632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_4974632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4974632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4974632 prefixEnd_4974632 := by exact prefixLift 4974632
  have htrace : WordTrace (prefixWord ++ tailWord_4974632) baseStart_4974632 baseEnd_4974632 := by
    simpa [prefixWord, tailWord_4974632, baseEnd_4974632] using wordTrace_append hprefix tailTrace_4974632
  have hstable : (prefixWord ++ tailWord_4974632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4974632).length < 2 ^ (prefixWord ++ tailWord_4974632).sum := by decide
  have hdescent : baseEnd_4974632 < baseStart_4974632 := by decide
  rcases family_descends (prefixWord ++ tailWord_4974632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4974677 : List Nat := [1, 3, 2, 2, 1, 4, 2, 3, 5]
def baseStart_4974677 : Nat := 118140960795 + 4974677 * 2 ^ 59
def prefixEnd_4974677 : Nat := 4983230072969 + 3 ^ 40 * 4974677 * 2
def baseEnd_4974677 : Nat := 283822266874082031895487

theorem tailTrace_4974677 : CollatzResearch.WordTrace tailWord_4974677 prefixEnd_4974677 283822266874082031895487 := by
  unfold tailWord_4974677
  simp only [CollatzResearch.WordTrace]
  refine ⟨181441376198602311036026285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120960917465734874024017523 181441376198602311036026285)
  ·
    refine ⟨68040516074475866638509857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181441376198602311036026285 68040516074475866638509857)
    ·
      refine ⟨51030387055856899978882393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68040516074475866638509857 51030387055856899978882393)
      ·
        refine ⟨38272790291892674984161795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51030387055856899978882393 38272790291892674984161795)
        ·
          refine ⟨57409185437839012476242693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38272790291892674984161795 57409185437839012476242693)
          ·
            refine ⟨10764222269594814839295505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57409185437839012476242693 10764222269594814839295505)
            ·
              refine ⟨8073166702196111129471629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10764222269594814839295505 8073166702196111129471629)
              ·
                refine ⟨3027437513323541673551861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8073166702196111129471629 3027437513323541673551861)
                ·
                  refine ⟨283822266874082031895487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3027437513323541673551861 283822266874082031895487)
                  ·
                    rfl

theorem cell23_4974677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 3, 5].length) (baseStart_4974677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4974677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4974677 prefixEnd_4974677 := by exact prefixLift 4974677
  have htrace : WordTrace (prefixWord ++ tailWord_4974677) baseStart_4974677 baseEnd_4974677 := by
    simpa [prefixWord, tailWord_4974677, baseEnd_4974677] using wordTrace_append hprefix tailTrace_4974677
  have hstable : (prefixWord ++ tailWord_4974677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4974677).length < 2 ^ (prefixWord ++ tailWord_4974677).sum := by decide
  have hdescent : baseEnd_4974677 < baseStart_4974677 := by decide
  rcases family_descends (prefixWord ++ tailWord_4974677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4974754 : List Nat := [3, 3, 1, 3, 1, 1, 3, 1, 3, 4]
def baseStart_4974754 : Nat := 118140960795 + 4974754 * 2 ^ 59
def prefixEnd_4974754 : Nat := 4983230072969 + 3 ^ 40 * 4974754 * 2
def baseEnd_4974754 : Nat := 851479979959044828598843

theorem tailTrace_4974754 : CollatzResearch.WordTrace tailWord_4974754 prefixEnd_4974754 851479979959044828598843 := by
  unfold tailWord_4974754
  simp only [CollatzResearch.WordTrace]
  refine ⟨45361046154830838296644829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120962789746215568791052877 45361046154830838296644829)
  ·
    refine ⟨17010392308061564361241811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45361046154830838296644829 17010392308061564361241811)
    ·
      refine ⟨25515588462092346541862717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17010392308061564361241811 25515588462092346541862717)
      ·
        refine ⟨9568345673284629953198519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25515588462092346541862717 9568345673284629953198519)
        ·
          refine ⟨14352518509926944929797779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9568345673284629953198519 14352518509926944929797779)
          ·
            refine ⟨21528777764890417394696669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14352518509926944929797779 21528777764890417394696669)
            ·
              refine ⟨8073291661833906523011251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21528777764890417394696669 8073291661833906523011251)
              ·
                refine ⟨12109937492750859784516877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8073291661833906523011251 12109937492750859784516877)
                ·
                  refine ⟨4541226559781572419193829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12109937492750859784516877 4541226559781572419193829)
                  ·
                    refine ⟨851479979959044828598843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4541226559781572419193829 851479979959044828598843)
                    ·
                      rfl

theorem cell23_4974754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 1, 3, 4].length) (baseStart_4974754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4974754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4974754 prefixEnd_4974754 := by exact prefixLift 4974754
  have htrace : WordTrace (prefixWord ++ tailWord_4974754) baseStart_4974754 baseEnd_4974754 := by
    simpa [prefixWord, tailWord_4974754, baseEnd_4974754] using wordTrace_append hprefix tailTrace_4974754
  have hstable : (prefixWord ++ tailWord_4974754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4974754).length < 2 ^ (prefixWord ++ tailWord_4974754).sum := by decide
  have hdescent : baseEnd_4974754 < baseStart_4974754 := by decide
  rcases family_descends (prefixWord ++ tailWord_4974754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4974777 : List Nat := [1, 2, 1, 4, 1, 2, 2, 1, 5, 1, 3]
def baseStart_4974777 : Nat := 118140960795 + 4974777 * 2 ^ 59
def prefixEnd_4974777 : Nat := 4983230072969 + 3 ^ 40 * 4974777 * 2
def baseEnd_4974777 : Nat := 2554451749932187895808923

theorem tailTrace_4974777 : CollatzResearch.WordTrace tailWord_4974777 prefixEnd_4974777 2554451749932187895808923 := by
  unfold tailWord_4974777
  simp only [CollatzResearch.WordTrace]
  refine ⟨181445023498240028114666585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120963348998826685409777723 181445023498240028114666585)
  ·
    refine ⟨136083767623680021085999939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181445023498240028114666585 136083767623680021085999939)
    ·
      refine ⟨204125651435520031628999909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136083767623680021085999939 204125651435520031628999909)
      ·
        refine ⟨38273559644160005930437483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 204125651435520031628999909 38273559644160005930437483)
        ·
          refine ⟨57410339466240008895656225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38273559644160005930437483 57410339466240008895656225)
          ·
            refine ⟨43057754599680006671742169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57410339466240008895656225 43057754599680006671742169)
            ·
              refine ⟨32293315949760005003806627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43057754599680006671742169 32293315949760005003806627)
              ·
                refine ⟨48439973924640007505709941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32293315949760005003806627 48439973924640007505709941)
                ·
                  refine ⟨4541247555435000703660307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48439973924640007505709941 4541247555435000703660307)
                  ·
                    refine ⟨6811871333152501055490461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4541247555435000703660307 6811871333152501055490461)
                    ·
                      refine ⟨2554451749932187895808923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6811871333152501055490461 2554451749932187895808923)
                      ·
                        rfl

theorem cell23_4974777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 5, 1, 3].length) (baseStart_4974777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4974777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4974777 prefixEnd_4974777 := by exact prefixLift 4974777
  have htrace : WordTrace (prefixWord ++ tailWord_4974777) baseStart_4974777 baseEnd_4974777 := by
    simpa [prefixWord, tailWord_4974777, baseEnd_4974777] using wordTrace_append hprefix tailTrace_4974777
  have hstable : (prefixWord ++ tailWord_4974777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4974777).length < 2 ^ (prefixWord ++ tailWord_4974777).sum := by decide
  have hdescent : baseEnd_4974777 < baseStart_4974777 := by decide
  rcases family_descends (prefixWord ++ tailWord_4974777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4974805 : List Nat := [1, 3, 2, 4, 3, 1, 2, 2, 1, 4]
def baseStart_4974805 : Nat := 118140960795 + 4974805 * 2 ^ 59
def prefixEnd_4974805 : Nat := 4983230072969 + 3 ^ 40 * 4974805 * 2
def baseEnd_4974805 : Nat := 851488709130171262086265

theorem tailTrace_4974805 : CollatzResearch.WordTrace tailWord_4974805 prefixEnd_4974805 851488709130171262086265 := by
  unfold tailWord_4974805
  simp only [CollatzResearch.WordTrace]
  refine ⟨181446044742138588896685869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120964029828092392597790579 181446044742138588896685869)
  ·
    refine ⟨68042266778301970836257201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181446044742138588896685869 68042266778301970836257201)
    ·
      refine ⟨51031700083726478127192901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68042266778301970836257201 51031700083726478127192901)
      ·
        refine ⟨9568443765698714648848669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51031700083726478127192901 9568443765698714648848669)
        ·
          refine ⟨3588166412137017993318251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9568443765698714648848669 3588166412137017993318251)
          ·
            refine ⟨5382249618205526989977377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3588166412137017993318251 5382249618205526989977377)
            ·
              refine ⟨4036687213654145242483033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5382249618205526989977377 4036687213654145242483033)
              ·
                refine ⟨3027515410240608931862275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4036687213654145242483033 3027515410240608931862275)
                ·
                  refine ⟨4541273115360913397793413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3027515410240608931862275 4541273115360913397793413)
                  ·
                    refine ⟨851488709130171262086265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4541273115360913397793413 851488709130171262086265)
                    ·
                      rfl

theorem cell23_4974805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 2, 2, 1, 4].length) (baseStart_4974805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4974805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4974805 prefixEnd_4974805 := by exact prefixLift 4974805
  have htrace : WordTrace (prefixWord ++ tailWord_4974805) baseStart_4974805 baseEnd_4974805 := by
    simpa [prefixWord, tailWord_4974805, baseEnd_4974805] using wordTrace_append hprefix tailTrace_4974805
  have hstable : (prefixWord ++ tailWord_4974805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4974805).length < 2 ^ (prefixWord ++ tailWord_4974805).sum := by decide
  have hdescent : baseEnd_4974805 < baseStart_4974805 := by decide
  rcases family_descends (prefixWord ++ tailWord_4974805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4974820 : List Nat := [2, 3, 1, 1, 1, 2, 1, 3, 3, 1, 5]
def baseStart_4974820 : Nat := 118140960795 + 4974820 * 2 ^ 59
def prefixEnd_4974820 : Nat := 4983230072969 + 3 ^ 40 * 4974820 * 2
def baseEnd_4974820 : Nat := 2554473829600331227571225

theorem tailTrace_4974820 : CollatzResearch.WordTrace tailWord_4974820 prefixEnd_4974820 2554473829600331227571225 := by
  unfold tailWord_4974820
  simp only [CollatzResearch.WordTrace]
  refine ⟨90723295918542123229240957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120964394558056164305654609 90723295918542123229240957)
  ·
    refine ⟨34021235969453296210965359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90723295918542123229240957 34021235969453296210965359)
    ·
      refine ⟨51031853954179944316448039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34021235969453296210965359 51031853954179944316448039)
      ·
        refine ⟨76547780931269916474672059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51031853954179944316448039 76547780931269916474672059)
        ·
          refine ⟨114821671396904874712008089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76547780931269916474672059 114821671396904874712008089)
          ·
            refine ⟨86116253547678656034006067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114821671396904874712008089 86116253547678656034006067)
            ·
              refine ⟨129174380321517984051009101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86116253547678656034006067 129174380321517984051009101)
              ·
                refine ⟨48440392620569244019128413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 129174380321517984051009101 48440392620569244019128413)
                ·
                  refine ⟨18165147232713466507173155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48440392620569244019128413 18165147232713466507173155)
                  ·
                    refine ⟨27247720849070199760759733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18165147232713466507173155 27247720849070199760759733)
                    ·
                      refine ⟨2554473829600331227571225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27247720849070199760759733 2554473829600331227571225)
                      ·
                        rfl

theorem cell23_4974820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 3, 1, 5].length) (baseStart_4974820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4974820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4974820 prefixEnd_4974820 := by exact prefixLift 4974820
  have htrace : WordTrace (prefixWord ++ tailWord_4974820) baseStart_4974820 baseEnd_4974820 := by
    simpa [prefixWord, tailWord_4974820, baseEnd_4974820] using wordTrace_append hprefix tailTrace_4974820
  have hstable : (prefixWord ++ tailWord_4974820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4974820).length < 2 ^ (prefixWord ++ tailWord_4974820).sum := by decide
  have hdescent : baseEnd_4974820 < baseStart_4974820 := by decide
  rcases family_descends (prefixWord ++ tailWord_4974820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4974827 : List Nat := [1, 1, 1, 1, 2, 5, 1, 5, 2, 4]
def baseStart_4974827 : Nat := 118140960795 + 4974827 * 2 ^ 59
def prefixEnd_4974827 : Nat := 4983230072969 + 3 ^ 40 * 4974827 * 2
def baseEnd_4974827 : Nat := 851492474654970900061231

theorem tailTrace_4974827 : CollatzResearch.WordTrace tailWord_4974827 prefixEnd_4974827 851492474654970900061231 := by
  unfold tailWord_4974827
  simp only [CollatzResearch.WordTrace]
  refine ⟨181446847148058886653986735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120964564765372591102657823 181446847148058886653986735)
  ·
    refine ⟨272170270722088329980980103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181446847148058886653986735 272170270722088329980980103)
    ·
      refine ⟨408255406083132494971470155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272170270722088329980980103 408255406083132494971470155)
      ·
        refine ⟨612383109124698742457205233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 408255406083132494971470155 612383109124698742457205233)
        ·
          refine ⟨459287331843524056842903925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 612383109124698742457205233 459287331843524056842903925)
          ·
            refine ⟨43058187360330380329022243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 459287331843524056842903925 43058187360330380329022243)
            ·
              refine ⟨64587281040495570493533365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43058187360330380329022243 64587281040495570493533365)
              ·
                refine ⟨6055057597546459733768753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 64587281040495570493533365 6055057597546459733768753)
                ·
                  refine ⟨4541293198159844800326565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6055057597546459733768753 4541293198159844800326565)
                  ·
                    refine ⟨851492474654970900061231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4541293198159844800326565 851492474654970900061231)
                    ·
                      rfl

theorem cell23_4974827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 5, 2, 4].length) (baseStart_4974827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4974827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4974827 prefixEnd_4974827 := by exact prefixLift 4974827
  have htrace : WordTrace (prefixWord ++ tailWord_4974827) baseStart_4974827 baseEnd_4974827 := by
    simpa [prefixWord, tailWord_4974827, baseEnd_4974827] using wordTrace_append hprefix tailTrace_4974827
  have hstable : (prefixWord ++ tailWord_4974827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4974827).length < 2 ^ (prefixWord ++ tailWord_4974827).sum := by decide
  have hdescent : baseEnd_4974827 < baseStart_4974827 := by decide
  rcases family_descends (prefixWord ++ tailWord_4974827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4974884 : List Nat := [2, 3, 1, 3, 1, 2, 3, 1, 1, 3, 3]
def baseStart_4974884 : Nat := 118140960795 + 4974884 * 2 ^ 59
def prefixEnd_4974884 : Nat := 4983230072969 + 3 ^ 40 * 4974884 * 2
def baseEnd_4974884 : Nat := 2554506692362218977170931

theorem tailTrace_4974884 : CollatzResearch.WordTrace tailWord_4974884 prefixEnd_4974884 2554506692362218977170931 := by
  unfold tailWord_4974884
  simp only [CollatzResearch.WordTrace]
  refine ⟨90724463054426192694405853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120965950739234923592541137 90724463054426192694405853)
  ·
    refine ⟨34021673645409822260402195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90724463054426192694405853 34021673645409822260402195)
    ·
      refine ⟨51032510468114733390603293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34021673645409822260402195 51032510468114733390603293)
      ·
        refine ⟨19137191425543025021476235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51032510468114733390603293 19137191425543025021476235)
        ·
          refine ⟨28705787138314537532214353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19137191425543025021476235 28705787138314537532214353)
          ·
            refine ⟨21529340353735903149160765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28705787138314537532214353 21529340353735903149160765)
            ·
              refine ⟨8073502632650963680935287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21529340353735903149160765 8073502632650963680935287)
              ·
                refine ⟨12110253948976445521402931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8073502632650963680935287 12110253948976445521402931)
                ·
                  refine ⟨18165380923464668282104397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12110253948976445521402931 18165380923464668282104397)
                  ·
                    refine ⟨6812017846299250605789149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18165380923464668282104397 6812017846299250605789149)
                    ·
                      refine ⟨2554506692362218977170931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6812017846299250605789149 2554506692362218977170931)
                      ·
                        rfl

theorem cell23_4974884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_4974884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4974884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4974884 prefixEnd_4974884 := by exact prefixLift 4974884
  have htrace : WordTrace (prefixWord ++ tailWord_4974884) baseStart_4974884 baseEnd_4974884 := by
    simpa [prefixWord, tailWord_4974884, baseEnd_4974884] using wordTrace_append hprefix tailTrace_4974884
  have hstable : (prefixWord ++ tailWord_4974884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4974884).length < 2 ^ (prefixWord ++ tailWord_4974884).sum := by decide
  have hdescent : baseEnd_4974884 < baseStart_4974884 := by decide
  rcases family_descends (prefixWord ++ tailWord_4974884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4974984 : List Nat := [2, 1, 3, 3, 1, 1, 1, 1, 1, 7, 2]
def baseStart_4974984 : Nat := 118140960795 + 4974984 * 2 ^ 59
def prefixEnd_4974984 : Nat := 4983230072969 + 3 ^ 40 * 4974984 * 2
def baseEnd_4974984 : Nat := 2554558040427668585920471

theorem tailTrace_4974984 : CollatzResearch.WordTrace tailWord_4974984 prefixEnd_4974984 2554558040427668585920471 := by
  unfold tailWord_4974984
  simp only [CollatzResearch.WordTrace]
  refine ⟨90726286704245051233726003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120968382272326734978301337 90726286704245051233726003)
  ·
    refine ⟨136089430056367576850589005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90726286704245051233726003 136089430056367576850589005)
    ·
      refine ⟨51033536271137841318970877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136089430056367576850589005 51033536271137841318970877)
      ·
        refine ⟨19137576101676690494614079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51033536271137841318970877 19137576101676690494614079)
        ·
          refine ⟨28706364152515035741921119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19137576101676690494614079 28706364152515035741921119)
          ·
            refine ⟨43059546228772553612881679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28706364152515035741921119 43059546228772553612881679)
            ·
              refine ⟨64589319343158830419322519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43059546228772553612881679 64589319343158830419322519)
              ·
                refine ⟨96883979014738245628983779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64589319343158830419322519 96883979014738245628983779)
                ·
                  refine ⟨145325968522107368443475669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96883979014738245628983779 145325968522107368443475669)
                  ·
                    refine ⟨3406077387236891447893961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 145325968522107368443475669 3406077387236891447893961)
                    ·
                      refine ⟨2554558040427668585920471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3406077387236891447893961 2554558040427668585920471)
                      ·
                        rfl

theorem cell23_4974984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 1, 7, 2].length) (baseStart_4974984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4974984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4974984 prefixEnd_4974984 := by exact prefixLift 4974984
  have htrace : WordTrace (prefixWord ++ tailWord_4974984) baseStart_4974984 baseEnd_4974984 := by
    simpa [prefixWord, tailWord_4974984, baseEnd_4974984] using wordTrace_append hprefix tailTrace_4974984
  have hstable : (prefixWord ++ tailWord_4974984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4974984).length < 2 ^ (prefixWord ++ tailWord_4974984).sum := by decide
  have hdescent : baseEnd_4974984 < baseStart_4974984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4974984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4974987 : List Nat := [1, 1, 1, 1, 4, 4, 2, 1, 1, 2, 5]
def baseStart_4974987 : Nat := 118140960795 + 4974987 * 2 ^ 59
def prefixEnd_4974987 : Nat := 4983230072969 + 3 ^ 40 * 4974987 * 2
def baseEnd_4974987 : Nat := 2554559580869632074182957

theorem tailTrace_4974987 : CollatzResearch.WordTrace tailWord_4974987 prefixEnd_4974987 2554559580869632074182957 := by
  unfold tailWord_4974987
  simp only [CollatzResearch.WordTrace]
  refine ⟨181452682827479233979811215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120968455218319489319874143 181452682827479233979811215)
  ·
    refine ⟨272179024241218850969716823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181452682827479233979811215 272179024241218850969716823)
    ·
      refine ⟨408268536361828276454575235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272179024241218850969716823 408268536361828276454575235)
      ·
        refine ⟨612402804542742414681862853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 408268536361828276454575235 612402804542742414681862853)
        ·
          refine ⟨114825525851764202752849285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 612402804542742414681862853 114825525851764202752849285)
          ·
            refine ⟨21529786097205788016159241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 114825525851764202752849285 21529786097205788016159241)
            ·
              refine ⟨16147339572904341012119431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21529786097205788016159241 16147339572904341012119431)
              ·
                refine ⟨24221009359356511518179147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16147339572904341012119431 24221009359356511518179147)
                ·
                  refine ⟨36331514039034767277268721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24221009359356511518179147 36331514039034767277268721)
                  ·
                    refine ⟨27248635529276075457951541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36331514039034767277268721 27248635529276075457951541)
                    ·
                      refine ⟨2554559580869632074182957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27248635529276075457951541 2554559580869632074182957)
                      ·
                        rfl

theorem cell23_4974987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 2, 5].length) (baseStart_4974987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4974987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4974987 prefixEnd_4974987 := by exact prefixLift 4974987
  have htrace : WordTrace (prefixWord ++ tailWord_4974987) baseStart_4974987 baseEnd_4974987 := by
    simpa [prefixWord, tailWord_4974987, baseEnd_4974987] using wordTrace_append hprefix tailTrace_4974987
  have hstable : (prefixWord ++ tailWord_4974987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4974987).length < 2 ^ (prefixWord ++ tailWord_4974987).sum := by decide
  have hdescent : baseEnd_4974987 < baseStart_4974987 := by decide
  rcases family_descends (prefixWord ++ tailWord_4974987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4974997 : List Nat := [1, 3, 2, 1, 1, 2, 1, 4, 1, 3, 4]
def baseStart_4974997 : Nat := 118140960795 + 4974997 * 2 ^ 59
def prefixEnd_4974997 : Nat := 4983230072969 + 3 ^ 40 * 4974997 * 2
def baseEnd_4974997 : Nat := 2554564715676177035057911

theorem tailTrace_4974997 : CollatzResearch.WordTrace tailWord_4974997 prefixEnd_4974997 2554564715676177035057911 := by
  unfold tailWord_4974997
  simp only [CollatzResearch.WordTrace]
  refine ⟨181453047557443005687675245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120968698371628670458450163 181453047557443005687675245)
  ·
    refine ⟨68044892834041127132878217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181453047557443005687675245 68044892834041127132878217)
    ·
      refine ⟨51033669625530845349658663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68044892834041127132878217 51033669625530845349658663)
      ·
        refine ⟨76550504438296268024487995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51033669625530845349658663 76550504438296268024487995)
        ·
          refine ⟨114825756657444402036731993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76550504438296268024487995 114825756657444402036731993)
          ·
            refine ⟨86119317493083301527548995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114825756657444402036731993 86119317493083301527548995)
            ·
              refine ⟨129178976239624952291323493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86119317493083301527548995 129178976239624952291323493)
              ·
                refine ⟨24221058044929678554623155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 129178976239624952291323493 24221058044929678554623155)
                ·
                  refine ⟨36331587067394517831934733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24221058044929678554623155 36331587067394517831934733)
                  ·
                    refine ⟨13624345150272944186975525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36331587067394517831934733 13624345150272944186975525)
                    ·
                      refine ⟨2554564715676177035057911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13624345150272944186975525 2554564715676177035057911)
                      ·
                        rfl

theorem cell23_4974997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 3, 4].length) (baseStart_4974997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4974997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4974997 prefixEnd_4974997 := by exact prefixLift 4974997
  have htrace : WordTrace (prefixWord ++ tailWord_4974997) baseStart_4974997 baseEnd_4974997 := by
    simpa [prefixWord, tailWord_4974997, baseEnd_4974997] using wordTrace_append hprefix tailTrace_4974997
  have hstable : (prefixWord ++ tailWord_4974997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4974997).length < 2 ^ (prefixWord ++ tailWord_4974997).sum := by decide
  have hdescent : baseEnd_4974997 < baseStart_4974997 := by decide
  rcases family_descends (prefixWord ++ tailWord_4974997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4975034 : List Nat := [3, 1, 1, 1, 2, 1, 1, 6, 2, 2, 3]
def baseStart_4975034 : Nat := 118140960795 + 4975034 * 2 ^ 59
def prefixEnd_4975034 : Nat := 4983230072969 + 3 ^ 40 * 4975034 * 2
def baseEnd_4975034 : Nat := 2554583714460393390295241

theorem tailTrace_4975034 : CollatzResearch.WordTrace tailWord_4975034 prefixEnd_4975034 2554583714460393390295241 := by
  unfold tailWord_4975034
  simp only [CollatzResearch.WordTrace]
  refine ⟨45363599264577240251693039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120969598038872640671181437 45363599264577240251693039)
  ·
    refine ⟨68045398896865860377539559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45363599264577240251693039 68045398896865860377539559)
    ·
      refine ⟨102068098345298790566309339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68045398896865860377539559 102068098345298790566309339)
      ·
        refine ⟨153102147517948185849464009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102068098345298790566309339 153102147517948185849464009)
        ·
          refine ⟨114826610638461139387098007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153102147517948185849464009 114826610638461139387098007)
          ·
            refine ⟨172239915957691709080647011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114826610638461139387098007 172239915957691709080647011)
            ·
              refine ⟨258359873936537563620970517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172239915957691709080647011 258359873936537563620970517)
              ·
                refine ⟨12110619090775198294732993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 258359873936537563620970517 12110619090775198294732993)
                ·
                  refine ⟨9082964318081398721049745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12110619090775198294732993 9082964318081398721049745)
                  ·
                    refine ⟨6812223238561049040787309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9082964318081398721049745 6812223238561049040787309)
                    ·
                      refine ⟨2554583714460393390295241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6812223238561049040787309 2554583714460393390295241)
                      ·
                        rfl

theorem cell23_4975034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 6, 2, 2, 3].length) (baseStart_4975034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4975034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4975034 prefixEnd_4975034 := by exact prefixLift 4975034
  have htrace : WordTrace (prefixWord ++ tailWord_4975034) baseStart_4975034 baseEnd_4975034 := by
    simpa [prefixWord, tailWord_4975034, baseEnd_4975034] using wordTrace_append hprefix tailTrace_4975034
  have hstable : (prefixWord ++ tailWord_4975034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4975034).length < 2 ^ (prefixWord ++ tailWord_4975034).sum := by decide
  have hdescent : baseEnd_4975034 < baseStart_4975034 := by decide
  rcases family_descends (prefixWord ++ tailWord_4975034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4975075 : List Nat := [1, 1, 1, 6, 3, 2, 1, 3, 1, 4]
def baseStart_4975075 : Nat := 118140960795 + 4975075 * 2 ^ 59
def prefixEnd_4975075 : Nat := 4983230072969 + 3 ^ 40 * 4975075 * 2
def baseEnd_4975075 : Nat := 851534922389075909960851

theorem tailTrace_4975075 : CollatzResearch.WordTrace tailWord_4975075 prefixEnd_4975075 851534922389075909960851 := by
  unfold tailWord_4975075
  simp only [CollatzResearch.WordTrace]
  refine ⟨181455892451160425009014679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120970594967440283339343119 181455892451160425009014679)
  ·
    refine ⟨272183838676740637513522019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181455892451160425009014679 272183838676740637513522019)
    ·
      refine ⟨408275758015110956270283029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272183838676740637513522019 408275758015110956270283029)
      ·
        refine ⟨19137926156958326075169517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 408275758015110956270283029 19137926156958326075169517)
        ·
          refine ⟨7176722308859372278188569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19137926156958326075169517 7176722308859372278188569)
          ·
            refine ⟨5382541731644529208641427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7176722308859372278188569 5382541731644529208641427)
            ·
              refine ⟨8073812597466793812962141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5382541731644529208641427 8073812597466793812962141)
              ·
                refine ⟨3027679724050047679860803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8073812597466793812962141 3027679724050047679860803)
                ·
                  refine ⟨4541519586075071519791205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3027679724050047679860803 4541519586075071519791205)
                  ·
                    refine ⟨851534922389075909960851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4541519586075071519791205 851534922389075909960851)
                    ·
                      rfl

theorem cell23_4975075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 3, 1, 4].length) (baseStart_4975075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4975075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4975075 prefixEnd_4975075 := by exact prefixLift 4975075
  have htrace : WordTrace (prefixWord ++ tailWord_4975075) baseStart_4975075 baseEnd_4975075 := by
    simpa [prefixWord, tailWord_4975075, baseEnd_4975075] using wordTrace_append hprefix tailTrace_4975075
  have hstable : (prefixWord ++ tailWord_4975075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4975075).length < 2 ^ (prefixWord ++ tailWord_4975075).sum := by decide
  have hdescent : baseEnd_4975075 < baseStart_4975075 := by decide
  rcases family_descends (prefixWord ++ tailWord_4975075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4975084 : List Nat := [2, 2, 1, 1, 2, 1, 3, 5, 1, 5]
def baseStart_4975084 : Nat := 118140960795 + 4975084 * 2 ^ 59
def prefixEnd_4975084 : Nat := 4983230072969 + 3 ^ 40 * 4975084 * 2
def baseEnd_4975084 : Nat := 851536462831039398223337

theorem tailTrace_4975084 : CollatzResearch.WordTrace tailWord_4975084 prefixEnd_4975084 851536462831039398223337 := by
  unfold tailWord_4975084
  simp only [CollatzResearch.WordTrace]
  refine ⟨90728110354063909773046153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120970813805418546364061537 90728110354063909773046153)
  ·
    refine ⟨68046082765547932329784615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90728110354063909773046153 68046082765547932329784615)
    ·
      refine ⟨102069124148321898494676923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68046082765547932329784615 102069124148321898494676923)
      ·
        refine ⟨153103686222482847742015385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102069124148321898494676923 153103686222482847742015385)
        ·
          refine ⟨114827764666862135806511539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153103686222482847742015385 114827764666862135806511539)
          ·
            refine ⟨172241647000293203709767309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114827764666862135806511539 172241647000293203709767309)
            ·
              refine ⟨64590617625109951391162741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 172241647000293203709767309 64590617625109951391162741)
              ·
                refine ⟨6055370402354057942921507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 64590617625109951391162741 6055370402354057942921507)
                ·
                  refine ⟨9083055603531086914382261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6055370402354057942921507 9083055603531086914382261)
                  ·
                    refine ⟨851536462831039398223337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9083055603531086914382261 851536462831039398223337)
                    ·
                      rfl

theorem cell23_4975084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 5].length) (baseStart_4975084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4975084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4975084 prefixEnd_4975084 := by exact prefixLift 4975084
  have htrace : WordTrace (prefixWord ++ tailWord_4975084) baseStart_4975084 baseEnd_4975084 := by
    simpa [prefixWord, tailWord_4975084, baseEnd_4975084] using wordTrace_append hprefix tailTrace_4975084
  have hstable : (prefixWord ++ tailWord_4975084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4975084).length < 2 ^ (prefixWord ++ tailWord_4975084).sum := by decide
  have hdescent : baseEnd_4975084 < baseStart_4975084 := by decide
  rcases family_descends (prefixWord ++ tailWord_4975084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4975091 : List Nat := [1, 1, 1, 2, 2, 2, 5, 2, 2, 3, 2]
def baseStart_4975091 : Nat := 118140960795 + 4975091 * 2 ^ 59
def prefixEnd_4975091 : Nat := 4983230072969 + 3 ^ 40 * 4975091 * 2
def baseEnd_4975091 : Nat := 2554612982857699667282479

theorem tailTrace_4975091 : CollatzResearch.WordTrace tailWord_4975091 prefixEnd_4975091 2554612982857699667282479 := by
  unfold tailWord_4975091
  simp only [CollatzResearch.WordTrace]
  refine ⟨181456476019102459741597127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120970984012734973161064751 181456476019102459741597127)
  ·
    refine ⟨272184714028653689612395691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181456476019102459741597127 272184714028653689612395691)
    ·
      refine ⟨408277071042980534418593537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272184714028653689612395691 408277071042980534418593537)
      ·
        refine ⟨306207803282235400813945153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 408277071042980534418593537 306207803282235400813945153)
        ·
          refine ⟨229655852461676550610458865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 306207803282235400813945153 229655852461676550610458865)
          ·
            refine ⟨172241889346257412957844149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 229655852461676550610458865 172241889346257412957844149)
            ·
              refine ⟨16147677126211632464797889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 172241889346257412957844149 16147677126211632464797889)
              ·
                refine ⟨12110757844658724348598417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16147677126211632464797889 12110757844658724348598417)
                ·
                  refine ⟨9083068383494043261448813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12110757844658724348598417 9083068383494043261448813)
                  ·
                    refine ⟨3406150643810266223043305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9083068383494043261448813 3406150643810266223043305)
                    ·
                      refine ⟨2554612982857699667282479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3406150643810266223043305 2554612982857699667282479)
                      ·
                        rfl

theorem cell23_4975091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 2, 2, 3, 2].length) (baseStart_4975091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4975091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4975091 prefixEnd_4975091 := by exact prefixLift 4975091
  have htrace : WordTrace (prefixWord ++ tailWord_4975091) baseStart_4975091 baseEnd_4975091 := by
    simpa [prefixWord, tailWord_4975091, baseEnd_4975091] using wordTrace_append hprefix tailTrace_4975091
  have hstable : (prefixWord ++ tailWord_4975091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4975091).length < 2 ^ (prefixWord ++ tailWord_4975091).sum := by decide
  have hdescent : baseEnd_4975091 < baseStart_4975091 := by decide
  rcases family_descends (prefixWord ++ tailWord_4975091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4975114 : List Nat := [3, 1, 2, 2, 2, 1, 2, 3, 1, 6]
def baseStart_4975114 : Nat := 118140960795 + 4975114 * 2 ^ 59
def prefixEnd_4975114 : Nat := 4983230072969 + 3 ^ 40 * 4975114 * 2
def baseEnd_4975114 : Nat := 851541597637584359098291

theorem tailTrace_4975114 : CollatzResearch.WordTrace tailWord_4975114 prefixEnd_4975114 851541597637584359098291 := by
  unfold tailWord_4975114
  simp only [CollatzResearch.WordTrace]
  refine ⟨45364328724504783667421099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120971543265346089779789597 45364328724504783667421099)
  ·
    refine ⟨68046493086757175501131649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45364328724504783667421099 68046493086757175501131649)
    ·
      refine ⟨51034869815067881625848737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68046493086757175501131649 51034869815067881625848737)
      ·
        refine ⟨38276152361300911219386553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51034869815067881625848737 38276152361300911219386553)
        ·
          refine ⟨28707114270975683414539915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38276152361300911219386553 28707114270975683414539915)
          ·
            refine ⟨43060671406463525121809873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28707114270975683414539915 43060671406463525121809873)
            ·
              refine ⟨32295503554847643841357405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43060671406463525121809873 32295503554847643841357405)
              ·
                refine ⟨12110813833067866440509027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32295503554847643841357405 12110813833067866440509027)
                ·
                  refine ⟨18166220749601799660763541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12110813833067866440509027 18166220749601799660763541)
                  ·
                    refine ⟨851541597637584359098291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18166220749601799660763541 851541597637584359098291)
                    ·
                      rfl

theorem cell23_4975114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 3, 1, 6].length) (baseStart_4975114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4975114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4975114 prefixEnd_4975114 := by exact prefixLift 4975114
  have htrace : WordTrace (prefixWord ++ tailWord_4975114) baseStart_4975114 baseEnd_4975114 := by
    simpa [prefixWord, tailWord_4975114, baseEnd_4975114] using wordTrace_append hprefix tailTrace_4975114
  have hstable : (prefixWord ++ tailWord_4975114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4975114).length < 2 ^ (prefixWord ++ tailWord_4975114).sum := by decide
  have hdescent : baseEnd_4975114 < baseStart_4975114 := by decide
  rcases family_descends (prefixWord ++ tailWord_4975114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4975118 : List Nat := [4, 1, 1, 2, 3, 3, 1, 2, 1, 5]
def baseStart_4975118 : Nat := 118140960795 + 4975118 * 2 ^ 59
def prefixEnd_4975118 : Nat := 4983230072969 + 3 ^ 40 * 4975118 * 2
def baseEnd_4975118 : Nat := 851542282278457020548285

theorem tailTrace_4975118 : CollatzResearch.WordTrace tailWord_4975118 prefixEnd_4975118 851542282278457020548285 := by
  unfold tailWord_4975118
  simp only [CollatzResearch.WordTrace]
  refine ⟨22682182598750580419103751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120971640526669762235220005 22682182598750580419103751)
  ·
    refine ⟨34023273898125870628655627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22682182598750580419103751 34023273898125870628655627)
    ·
      refine ⟨51034910847188805942983441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34023273898125870628655627 51034910847188805942983441)
      ·
        refine ⟨38276183135391604457237581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51034910847188805942983441 38276183135391604457237581)
        ·
          refine ⟨14353568675771851671464093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38276183135391604457237581 14353568675771851671464093)
          ·
            refine ⟨5382588253414444376799035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14353568675771851671464093 5382588253414444376799035)
            ·
              refine ⟨8073882380121666565198553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5382588253414444376799035 8073882380121666565198553)
              ·
                refine ⟨6055411785091249923898915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8073882380121666565198553 6055411785091249923898915)
                ·
                  refine ⟨9083117677636874885848373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6055411785091249923898915 9083117677636874885848373)
                  ·
                    refine ⟨851542282278457020548285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9083117677636874885848373 851542282278457020548285)
                    ·
                      rfl

theorem cell23_4975118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 2, 1, 5].length) (baseStart_4975118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4975118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4975118 prefixEnd_4975118 := by exact prefixLift 4975118
  have htrace : WordTrace (prefixWord ++ tailWord_4975118) baseStart_4975118 baseEnd_4975118 := by
    simpa [prefixWord, tailWord_4975118, baseEnd_4975118] using wordTrace_append hprefix tailTrace_4975118
  have hstable : (prefixWord ++ tailWord_4975118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4975118).length < 2 ^ (prefixWord ++ tailWord_4975118).sum := by decide
  have hdescent : baseEnd_4975118 < baseStart_4975118 := by decide
  rcases family_descends (prefixWord ++ tailWord_4975118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4975141 : List Nat := [1, 3, 1, 2, 2, 1, 2, 5, 1, 2, 3]
def baseStart_4975141 : Nat := 118140960795 + 4975141 * 2 ^ 59
def prefixEnd_4975141 : Nat := 4983230072969 + 3 ^ 40 * 4975141 * 2
def baseEnd_4975141 : Nat := 2554638656890424471657249

theorem tailTrace_4975141 : CollatzResearch.WordTrace tailWord_4975141 prefixEnd_4975141 2554638656890424471657249 := by
  unfold tailWord_4975141
  simp only [CollatzResearch.WordTrace]
  refine ⟨181458299668921318280917277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120972199779280878853944851 181458299668921318280917277)
  ·
    refine ⟨68046862375845494355343979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181458299668921318280917277 68046862375845494355343979)
    ·
      refine ⟨102070293563768241533015969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68046862375845494355343979 102070293563768241533015969)
      ·
        refine ⟨76552720172826181149761977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102070293563768241533015969 76552720172826181149761977)
        ·
          refine ⟨57414540129619635862321483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76552720172826181149761977 57414540129619635862321483)
          ·
            refine ⟨86121810194429453793482225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57414540129619635862321483 86121810194429453793482225)
            ·
              refine ⟨64591357645822090345111669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86121810194429453793482225 64591357645822090345111669)
              ·
                refine ⟨6055439779295820969854219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 64591357645822090345111669 6055439779295820969854219)
                ·
                  refine ⟨9083159668943731454781329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6055439779295820969854219 9083159668943731454781329)
                  ·
                    refine ⟨6812369751707798591085997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9083159668943731454781329 6812369751707798591085997)
                    ·
                      refine ⟨2554638656890424471657249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6812369751707798591085997 2554638656890424471657249)
                      ·
                        rfl

theorem cell23_4975141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 5, 1, 2, 3].length) (baseStart_4975141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4975141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4975141 prefixEnd_4975141 := by exact prefixLift 4975141
  have htrace : WordTrace (prefixWord ++ tailWord_4975141) baseStart_4975141 baseEnd_4975141 := by
    simpa [prefixWord, tailWord_4975141, baseEnd_4975141] using wordTrace_append hprefix tailTrace_4975141
  have hstable : (prefixWord ++ tailWord_4975141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4975141).length < 2 ^ (prefixWord ++ tailWord_4975141).sum := by decide
  have hdescent : baseEnd_4975141 < baseStart_4975141 := by decide
  rcases family_descends (prefixWord ++ tailWord_4975141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4975144 : List Nat := [2, 1, 5, 2, 1, 12]
def baseStart_4975144 : Nat := 118140960795 + 4975144 * 2 ^ 59
def prefixEnd_4975144 : Nat := 4983230072969 + 3 ^ 40 * 4975144 * 2
def baseEnd_4975144 : Nat := 10512922622767028641645

theorem tailTrace_4975144 : CollatzResearch.WordTrace tailWord_4975144 prefixEnd_4975144 10512922622767028641645 := by
  unfold tailWord_4975144
  simp only [CollatzResearch.WordTrace]
  refine ⟨90729204543955224896638243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120972272725273633195517657 90729204543955224896638243)
  ·
    refine ⟨136093806815932837344957365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90729204543955224896638243 136093806815932837344957365)
    ·
      refine ⟨12758794388993703501089753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 136093806815932837344957365 12758794388993703501089753)
      ·
        refine ⟨9569095791745277625817315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12758794388993703501089753 9569095791745277625817315)
        ·
          refine ⟨14353643687617916438725973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9569095791745277625817315 14353643687617916438725973)
          ·
            refine ⟨10512922622767028641645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 14353643687617916438725973 10512922622767028641645)
            ·
              rfl

theorem cell23_4975144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 12].length) (baseStart_4975144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4975144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4975144 prefixEnd_4975144 := by exact prefixLift 4975144
  have htrace : WordTrace (prefixWord ++ tailWord_4975144) baseStart_4975144 baseEnd_4975144 := by
    simpa [prefixWord, tailWord_4975144, baseEnd_4975144] using wordTrace_append hprefix tailTrace_4975144
  have hstable : (prefixWord ++ tailWord_4975144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4975144).length < 2 ^ (prefixWord ++ tailWord_4975144).sum := by decide
  have hdescent : baseEnd_4975144 < baseStart_4975144 := by decide
  rcases family_descends (prefixWord ++ tailWord_4975144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4975155 : List Nat := [1, 1, 1, 2, 4, 2, 3, 4, 1, 2, 2]
def baseStart_4975155 : Nat := 118140960795 + 4975155 * 2 ^ 59
def prefixEnd_4975155 : Nat := 4983230072969 + 3 ^ 40 * 4975155 * 2
def baseEnd_4975155 : Nat := 2554645845619587416882185

theorem tailTrace_4975155 : CollatzResearch.WordTrace tailWord_4975155 prefixEnd_4975155 2554645845619587416882185 := by
  unfold tailWord_4975155
  simp only [CollatzResearch.WordTrace]
  refine ⟨181458810290870598671926919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120972540193913732447951279 181458810290870598671926919)
  ·
    refine ⟨272188215436305898007890379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181458810290870598671926919 272188215436305898007890379)
    ·
      refine ⟨408282323154458847011835569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272188215436305898007890379 408282323154458847011835569)
      ·
        refine ⟨306211742365844135258876677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 408282323154458847011835569 306211742365844135258876677)
        ·
          refine ⟨57414701693595775361039377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 306211742365844135258876677 57414701693595775361039377)
          ·
            refine ⟨43061026270196831520779533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57414701693595775361039377 43061026270196831520779533)
            ·
              refine ⟨16147884851323811820292325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43061026270196831520779533 16147884851323811820292325)
              ·
                refine ⟨3027728409623214716304811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16147884851323811820292325 3027728409623214716304811)
                ·
                  refine ⟨4541592614434822074457217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3027728409623214716304811 4541592614434822074457217)
                  ·
                    refine ⟨3406194460826116555842913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4541592614434822074457217 3406194460826116555842913)
                    ·
                      refine ⟨2554645845619587416882185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3406194460826116555842913 2554645845619587416882185)
                      ·
                        rfl

theorem cell23_4975155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 4, 1, 2, 2].length) (baseStart_4975155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4975155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4975155 prefixEnd_4975155 := by exact prefixLift 4975155
  have htrace : WordTrace (prefixWord ++ tailWord_4975155) baseStart_4975155 baseEnd_4975155 := by
    simpa [prefixWord, tailWord_4975155, baseEnd_4975155] using wordTrace_append hprefix tailTrace_4975155
  have hstable : (prefixWord ++ tailWord_4975155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4975155).length < 2 ^ (prefixWord ++ tailWord_4975155).sum := by decide
  have hdescent : baseEnd_4975155 < baseStart_4975155 := by decide
  rcases family_descends (prefixWord ++ tailWord_4975155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4975158 : List Nat := [5, 1, 2, 1, 2, 1, 1, 2, 3, 2, 3]
def baseStart_4975158 : Nat := 118140960795 + 4975158 * 2 ^ 59
def prefixEnd_4975158 : Nat := 4983230072969 + 3 ^ 40 * 4975158 * 2
def baseEnd_4975158 : Nat := 2554647386061550905144671

theorem tailTrace_4975158 : CollatzResearch.WordTrace tailWord_4975158 prefixEnd_4975158 2554647386061550905144671 := by
  unfold tailWord_4975158
  simp only [CollatzResearch.WordTrace]
  refine ⟨11341182481866233136517883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 120972613139906486789524085 11341182481866233136517883)
  ·
    refine ⟨17011773722799349704776825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11341182481866233136517883 17011773722799349704776825)
    ·
      refine ⟨12758830292099512278582619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17011773722799349704776825 12758830292099512278582619)
      ·
        refine ⟨19138245438149268417873929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12758830292099512278582619 19138245438149268417873929)
        ·
          refine ⟨14353684078611951313405447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19138245438149268417873929 14353684078611951313405447)
          ·
            refine ⟨21530526117917926970108171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14353684078611951313405447 21530526117917926970108171)
            ·
              refine ⟨32295789176876890455162257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21530526117917926970108171 32295789176876890455162257)
              ·
                refine ⟨24221841882657667841371693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32295789176876890455162257 24221841882657667841371693)
                ·
                  refine ⟨9083190705996625440514385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24221841882657667841371693 9083190705996625440514385)
                  ·
                    refine ⟨6812393029497469080385789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9083190705996625440514385 6812393029497469080385789)
                    ·
                      refine ⟨2554647386061550905144671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6812393029497469080385789 2554647386061550905144671)
                      ·
                        rfl

theorem cell23_4975158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_4975158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4975158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4975158 prefixEnd_4975158 := by exact prefixLift 4975158
  have htrace : WordTrace (prefixWord ++ tailWord_4975158) baseStart_4975158 baseEnd_4975158 := by
    simpa [prefixWord, tailWord_4975158, baseEnd_4975158] using wordTrace_append hprefix tailTrace_4975158
  have hstable : (prefixWord ++ tailWord_4975158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4975158).length < 2 ^ (prefixWord ++ tailWord_4975158).sum := by decide
  have hdescent : baseEnd_4975158 < baseStart_4975158 := by decide
  rcases family_descends (prefixWord ++ tailWord_4975158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4975204 : List Nat := [2, 3, 1, 1, 2, 2, 1, 1, 4, 6]
def baseStart_4975204 : Nat := 118140960795 + 4975204 * 2 ^ 59
def prefixEnd_4975204 : Nat := 4983230072969 + 3 ^ 40 * 4975204 * 2
def baseEnd_4975204 : Nat := 851557002057219241723153

theorem tailTrace_4975204 : CollatzResearch.WordTrace tailWord_4975204 prefixEnd_4975204 851557002057219241723153 := by
  unfold tailWord_4975204
  simp only [CollatzResearch.WordTrace]
  refine ⟨90730298733846540020230333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120973731645128720026973777 90730298733846540020230333)
  ·
    refine ⟨34023862025192452507586375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90730298733846540020230333 34023862025192452507586375)
    ·
      refine ⟨51035793037788678761379563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34023862025192452507586375 51035793037788678761379563)
      ·
        refine ⟨76553689556683018142069345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51035793037788678761379563 76553689556683018142069345)
        ·
          refine ⟨57415267167512263606552009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76553689556683018142069345 57415267167512263606552009)
          ·
            refine ⟨43061450375634197704914007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57415267167512263606552009 43061450375634197704914007)
            ·
              refine ⟨64592175563451296557371011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43061450375634197704914007 64592175563451296557371011)
              ·
                refine ⟨96888263345176944836056517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64592175563451296557371011 96888263345176944836056517)
                ·
                  refine ⟨18166549377220677156760597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 96888263345176944836056517 18166549377220677156760597)
                  ·
                    refine ⟨851557002057219241723153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18166549377220677156760597 851557002057219241723153)
                    ·
                      rfl

theorem cell23_4975204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 4, 6].length) (baseStart_4975204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4975204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4975204 prefixEnd_4975204 := by exact prefixLift 4975204
  have htrace : WordTrace (prefixWord ++ tailWord_4975204) baseStart_4975204 baseEnd_4975204 := by
    simpa [prefixWord, tailWord_4975204, baseEnd_4975204] using wordTrace_append hprefix tailTrace_4975204
  have hstable : (prefixWord ++ tailWord_4975204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4975204).length < 2 ^ (prefixWord ++ tailWord_4975204).sum := by decide
  have hdescent : baseEnd_4975204 < baseStart_4975204 := by decide
  rcases family_descends (prefixWord ++ tailWord_4975204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4975222 : List Nat := [5, 1, 1, 2, 4, 1, 1, 1, 1, 3, 3]
def baseStart_4975222 : Nat := 118140960795 + 4975222 * 2 ^ 59
def prefixEnd_4975222 : Nat := 4983230072969 + 3 ^ 40 * 4975222 * 2
def baseEnd_4975222 : Nat := 2554680248823438654744377

theorem tailTrace_4975222 : CollatzResearch.WordTrace tailWord_4975222 prefixEnd_4975222 2554680248823438654744377 := by
  unfold tailWord_4975222
  simp only [CollatzResearch.WordTrace]
  refine ⟨11341328373851741819663495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 120974169321085246076410613 11341328373851741819663495)
  ·
    refine ⟨17011992560777612729495243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11341328373851741819663495 17011992560777612729495243)
    ·
      refine ⟨25517988841166419094242865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17011992560777612729495243 25517988841166419094242865)
      ·
        refine ⟨19138491630874814320682149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25517988841166419094242865 19138491630874814320682149)
        ·
          refine ⟨3588467180789027685127903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19138491630874814320682149 3588467180789027685127903)
          ·
            refine ⟨5382700771183541527691855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3588467180789027685127903 5382700771183541527691855)
            ·
              refine ⟨8074051156775312291537783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5382700771183541527691855 8074051156775312291537783)
              ·
                refine ⟨12111076735162968437306675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8074051156775312291537783 12111076735162968437306675)
                ·
                  refine ⟨18166615102744452655960013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12111076735162968437306675 18166615102744452655960013)
                  ·
                    refine ⟨6812480663529169745985005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18166615102744452655960013 6812480663529169745985005)
                    ·
                      refine ⟨2554680248823438654744377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6812480663529169745985005 2554680248823438654744377)
                      ·
                        rfl

theorem cell23_4975222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 1, 1, 3, 3].length) (baseStart_4975222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4975222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4975222 prefixEnd_4975222 := by exact prefixLift 4975222
  have htrace : WordTrace (prefixWord ++ tailWord_4975222) baseStart_4975222 baseEnd_4975222 := by
    simpa [prefixWord, tailWord_4975222, baseEnd_4975222] using wordTrace_append hprefix tailTrace_4975222
  have hstable : (prefixWord ++ tailWord_4975222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4975222).length < 2 ^ (prefixWord ++ tailWord_4975222).sum := by decide
  have hdescent : baseEnd_4975222 < baseStart_4975222 := by decide
  rcases family_descends (prefixWord ++ tailWord_4975222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4975228 : List Nat := [2, 2, 2, 1, 1, 2, 5, 1, 1, 4, 2]
def baseStart_4975228 : Nat := 118140960795 + 4975228 * 2 ^ 59
def prefixEnd_4975228 : Nat := 4983230072969 + 3 ^ 40 * 4975228 * 2
def baseEnd_4975228 : Nat := 2554683329707365631269349

theorem tailTrace_4975228 : CollatzResearch.WordTrace tailWord_4975228 prefixEnd_4975228 2554683329707365631269349 := by
  unfold tailWord_4975228
  simp only [CollatzResearch.WordTrace]
  refine ⟨90730736409803066069667169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120974315213070754759556225 90730736409803066069667169)
  ·
    refine ⟨68048052307352299552250377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90730736409803066069667169 68048052307352299552250377)
    ·
      refine ⟨51036039230514224664187783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68048052307352299552250377 51036039230514224664187783)
      ·
        refine ⟨76554058845771336996281675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51036039230514224664187783 76554058845771336996281675)
        ·
          refine ⟨114831088268657005494422513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76554058845771336996281675 114831088268657005494422513)
          ·
            refine ⟨86123316201492754120816885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114831088268657005494422513 86123316201492754120816885)
            ·
              refine ⟨8074060893889945698826583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 86123316201492754120816885 8074060893889945698826583)
              ·
                refine ⟨12111091340834918548239875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8074060893889945698826583 12111091340834918548239875)
                ·
                  refine ⟨18166637011252377822359813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12111091340834918548239875 18166637011252377822359813)
                  ·
                    refine ⟨3406244439609820841692465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18166637011252377822359813 3406244439609820841692465)
                    ·
                      refine ⟨2554683329707365631269349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3406244439609820841692465 2554683329707365631269349)
                      ·
                        rfl

theorem cell23_4975228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 1, 1, 4, 2].length) (baseStart_4975228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4975228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4975228 prefixEnd_4975228 := by exact prefixLift 4975228
  have htrace : WordTrace (prefixWord ++ tailWord_4975228) baseStart_4975228 baseEnd_4975228 := by
    simpa [prefixWord, tailWord_4975228, baseEnd_4975228] using wordTrace_append hprefix tailTrace_4975228
  have hstable : (prefixWord ++ tailWord_4975228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4975228).length < 2 ^ (prefixWord ++ tailWord_4975228).sum := by decide
  have hdescent : baseEnd_4975228 < baseStart_4975228 := by decide
  rcases family_descends (prefixWord ++ tailWord_4975228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4975261 : List Nat := [1, 4, 2, 1, 1, 1, 2, 1, 4, 3, 3]
def baseStart_4975261 : Nat := 118140960795 + 4975261 * 2 ^ 59
def prefixEnd_4975261 : Nat := 4983230072969 + 3 ^ 40 * 4975261 * 2
def baseEnd_4975261 : Nat := 2554700274568964002156697

theorem tailTrace_4975261 : CollatzResearch.WordTrace tailWord_4975261 prefixEnd_4975261 2554700274568964002156697 := by
  unfold tailWord_4975261
  simp only [CollatzResearch.WordTrace]
  refine ⟨181462676428486578775285637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120975117618991052516857091 181462676428486578775285637)
  ·
    refine ⟨34024251830341233520366057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 181462676428486578775285637 34024251830341233520366057)
    ·
      refine ⟨25518188872755925140274543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34024251830341233520366057 25518188872755925140274543)
      ·
        refine ⟨38277283309133887710411815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25518188872755925140274543 38277283309133887710411815)
        ·
          refine ⟨57415924963700831565617723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38277283309133887710411815 57415924963700831565617723)
          ·
            refine ⟨86123887445551247348426585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57415924963700831565617723 86123887445551247348426585)
            ·
              refine ⟨64592915584163435511319939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86123887445551247348426585 64592915584163435511319939)
              ·
                refine ⟨96889373376245153266979909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64592915584163435511319939 96889373376245153266979909)
                ·
                  refine ⟨18166757508045966237558733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 96889373376245153266979909 18166757508045966237558733)
                  ·
                    refine ⟨6812534065517237339084525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18166757508045966237558733 6812534065517237339084525)
                    ·
                      refine ⟨2554700274568964002156697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6812534065517237339084525 2554700274568964002156697)
                      ·
                        rfl

theorem cell23_4975261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 4, 3, 3].length) (baseStart_4975261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4975261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4975261 prefixEnd_4975261 := by exact prefixLift 4975261
  have htrace : WordTrace (prefixWord ++ tailWord_4975261) baseStart_4975261 baseEnd_4975261 := by
    simpa [prefixWord, tailWord_4975261, baseEnd_4975261] using wordTrace_append hprefix tailTrace_4975261
  have hstable : (prefixWord ++ tailWord_4975261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4975261).length < 2 ^ (prefixWord ++ tailWord_4975261).sum := by decide
  have hdescent : baseEnd_4975261 < baseStart_4975261 := by decide
  rcases family_descends (prefixWord ++ tailWord_4975261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4975262 : List Nat := [4, 3, 1, 1, 1, 1, 2, 4, 2, 2, 2]
def baseStart_4975262 : Nat := 118140960795 + 4975262 * 2 ^ 59
def prefixEnd_4975262 : Nat := 4983230072969 + 3 ^ 40 * 4975262 * 2
def baseEnd_4975262 : Nat := 2554700788049618498244193

theorem tailTrace_4975262 : CollatzResearch.WordTrace tailWord_4975262 prefixEnd_4975262 2554700788049618498244193 := by
  unfold tailWord_4975262
  simp only [CollatzResearch.WordTrace]
  refine ⟨22682839112685369493259005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120975141934321970630714693 22682839112685369493259005)
  ·
    refine ⟨8506064667257013559972127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22682839112685369493259005 8506064667257013559972127)
    ·
      refine ⟨12759097000885520339958191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8506064667257013559972127 12759097000885520339958191)
      ·
        refine ⟨19138645501328280509937287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12759097000885520339958191 19138645501328280509937287)
        ·
          refine ⟨28707968251992420764905931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19138645501328280509937287 28707968251992420764905931)
          ·
            refine ⟨43061952377988631147358897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28707968251992420764905931 43061952377988631147358897)
            ·
              refine ⟨32296464283491473360519173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43061952377988631147358897 32296464283491473360519173)
              ·
                refine ⟨6055587053154651255097345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32296464283491473360519173 6055587053154651255097345)
                ·
                  refine ⟨4541690289865988441323009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6055587053154651255097345 4541690289865988441323009)
                  ·
                    refine ⟨3406267717399491330992257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4541690289865988441323009 3406267717399491330992257)
                    ·
                      refine ⟨2554700788049618498244193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3406267717399491330992257 2554700788049618498244193)
                      ·
                        rfl

theorem cell23_4975262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 4, 2, 2, 2].length) (baseStart_4975262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4975262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4975262 prefixEnd_4975262 := by exact prefixLift 4975262
  have htrace : WordTrace (prefixWord ++ tailWord_4975262) baseStart_4975262 baseEnd_4975262 := by
    simpa [prefixWord, tailWord_4975262, baseEnd_4975262] using wordTrace_append hprefix tailTrace_4975262
  have hstable : (prefixWord ++ tailWord_4975262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4975262).length < 2 ^ (prefixWord ++ tailWord_4975262).sum := by decide
  have hdescent : baseEnd_4975262 < baseStart_4975262 := by decide
  rcases family_descends (prefixWord ++ tailWord_4975262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4975349 : List Nat := [1, 3, 6, 1, 1, 2, 1, 1, 2, 5]
def baseStart_4975349 : Nat := 118140960795 + 4975349 * 2 ^ 59
def prefixEnd_4975349 : Nat := 4983230072969 + 3 ^ 40 * 4975349 * 2
def baseEnd_4975349 : Nat := 851581820288853219285431

theorem tailTrace_4975349 : CollatzResearch.WordTrace tailWord_4975349 prefixEnd_4975349 851581820288853219285431 := by
  unfold tailWord_4975349
  simp only [CollatzResearch.WordTrace]
  refine ⟨181465886052167769804489101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120977257368111846536326067 181465886052167769804489101)
  ·
    refine ⟨68049707269562913676683413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181465886052167769804489101 68049707269562913676683413)
    ·
      refine ⟨3189830028260761578594535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 68049707269562913676683413 3189830028260761578594535)
      ·
        refine ⟨4784745042391142367891803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3189830028260761578594535 4784745042391142367891803)
        ·
          refine ⟨7177117563586713551837705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4784745042391142367891803 7177117563586713551837705)
          ·
            refine ⟨5382838172690035163878279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7177117563586713551837705 5382838172690035163878279)
            ·
              refine ⟨8074257259035052745817419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5382838172690035163878279 8074257259035052745817419)
              ·
                refine ⟨12111385888552579118726129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8074257259035052745817419 12111385888552579118726129)
                ·
                  refine ⟨9083539416414434339044597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12111385888552579118726129 9083539416414434339044597)
                  ·
                    refine ⟨851581820288853219285431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9083539416414434339044597 851581820288853219285431)
                    ·
                      rfl

theorem cell23_4975349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_4975349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4975349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4975349 prefixEnd_4975349 := by exact prefixLift 4975349
  have htrace : WordTrace (prefixWord ++ tailWord_4975349) baseStart_4975349 baseEnd_4975349 := by
    simpa [prefixWord, tailWord_4975349, baseEnd_4975349] using wordTrace_append hprefix tailTrace_4975349
  have hstable : (prefixWord ++ tailWord_4975349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4975349).length < 2 ^ (prefixWord ++ tailWord_4975349).sum := by decide
  have hdescent : baseEnd_4975349 < baseStart_4975349 := by decide
  rcases family_descends (prefixWord ++ tailWord_4975349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4975362 : List Nat := [3, 4, 1, 1, 1, 2, 1, 5, 1, 4]
def baseStart_4975362 : Nat := 118140960795 + 4975362 * 2 ^ 59
def prefixEnd_4975362 : Nat := 4983230072969 + 3 ^ 40 * 4975362 * 2
def baseEnd_4975362 : Nat := 851584045371689368997911

theorem tailTrace_4975362 : CollatzResearch.WordTrace tailWord_4975362 prefixEnd_4975362 851584045371689368997911 := by
  unfold tailWord_4975362
  simp only [CollatzResearch.WordTrace]
  refine ⟨45366590050280168256178085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120977573467413782016474893 45366590050280168256178085)
  ·
    refine ⟨8506235634427531548033391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45366590050280168256178085 8506235634427531548033391)
    ·
      refine ⟨12759353451641297322050087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8506235634427531548033391 12759353451641297322050087)
      ·
        refine ⟨19139030177461945983075131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12759353451641297322050087 19139030177461945983075131)
        ·
          refine ⟨28708545266192918974612697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19139030177461945983075131 28708545266192918974612697)
          ·
            refine ⟨21531408949644689230959523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28708545266192918974612697 21531408949644689230959523)
            ·
              refine ⟨32297113424467033846439285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21531408949644689230959523 32297113424467033846439285)
              ·
                refine ⟨3027854383543784423103683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32297113424467033846439285 3027854383543784423103683)
                ·
                  refine ⟨4541781575315676634655525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3027854383543784423103683 4541781575315676634655525)
                  ·
                    refine ⟨851584045371689368997911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4541781575315676634655525 851584045371689368997911)
                    ·
                      rfl

theorem cell23_4975362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_4975362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4975362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4975362 prefixEnd_4975362 := by exact prefixLift 4975362
  have htrace : WordTrace (prefixWord ++ tailWord_4975362) baseStart_4975362 baseEnd_4975362 := by
    simpa [prefixWord, tailWord_4975362, baseEnd_4975362] using wordTrace_append hprefix tailTrace_4975362
  have hstable : (prefixWord ++ tailWord_4975362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4975362).length < 2 ^ (prefixWord ++ tailWord_4975362).sum := by decide
  have hdescent : baseEnd_4975362 < baseStart_4975362 := by decide
  rcases family_descends (prefixWord ++ tailWord_4975362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4975452 : List Nat := [2, 2, 4, 2, 1, 2, 1, 3, 2, 4]
def baseStart_4975452 : Nat := 118140960795 + 4975452 * 2 ^ 59
def prefixEnd_4975452 : Nat := 4983230072969 + 3 ^ 40 * 4975452 * 2
def baseEnd_4975452 : Nat := 851599449791324251622773

theorem tailTrace_4975452 : CollatzResearch.WordTrace tailWord_4975452 prefixEnd_4975452 851599449791324251622773 := by
  unfold tailWord_4975452
  simp only [CollatzResearch.WordTrace]
  refine ⟨90734821385397309197744305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120979761847196412263659073 90734821385397309197744305)
  ·
    refine ⟨68051116039047981898308229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90734821385397309197744305 68051116039047981898308229)
    ·
      refine ⟨12759584257321496605932793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68051116039047981898308229 12759584257321496605932793)
      ·
        refine ⟨9569688192991122454449595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12759584257321496605932793 9569688192991122454449595)
        ·
          refine ⟨14354532289486683681674393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9569688192991122454449595 14354532289486683681674393)
          ·
            refine ⟨10765899217115012761255795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14354532289486683681674393 10765899217115012761255795)
            ·
              refine ⟨16148848825672519141883693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10765899217115012761255795 16148848825672519141883693)
              ·
                refine ⟨6055818309627194678206385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16148848825672519141883693 6055818309627194678206385)
                ·
                  refine ⟨4541863732220396008654789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6055818309627194678206385 4541863732220396008654789)
                  ·
                    refine ⟨851599449791324251622773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4541863732220396008654789 851599449791324251622773)
                    ·
                      rfl

theorem cell23_4975452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_4975452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4975452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4975452 prefixEnd_4975452 := by exact prefixLift 4975452
  have htrace : WordTrace (prefixWord ++ tailWord_4975452) baseStart_4975452 baseEnd_4975452 := by
    simpa [prefixWord, tailWord_4975452, baseEnd_4975452] using wordTrace_append hprefix tailTrace_4975452
  have hstable : (prefixWord ++ tailWord_4975452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4975452).length < 2 ^ (prefixWord ++ tailWord_4975452).sum := by decide
  have hdescent : baseEnd_4975452 < baseStart_4975452 := by decide
  rcases family_descends (prefixWord ++ tailWord_4975452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4975471 : List Nat := [1, 1, 2, 1, 3, 1, 1, 3, 1, 4, 5]
def baseStart_4975471 : Nat := 118140960795 + 4975471 * 2 ^ 59
def prefixEnd_4975471 : Nat := 4983230072969 + 3 ^ 40 * 4975471 * 2
def baseEnd_4975471 : Nat := 2554808105506408180530731

theorem tailTrace_4975471 : CollatzResearch.WordTrace tailWord_4975471 prefixEnd_4975471 2554808105506408180530731 := by
  unfold tailWord_4975471
  simp only [CollatzResearch.WordTrace]
  refine ⟨181470335757725784640430267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120980223838483856426953511 181470335757725784640430267)
  ·
    refine ⟨272205503636588676960645401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181470335757725784640430267 272205503636588676960645401)
    ·
      refine ⟨204154127727441507720484051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 272205503636588676960645401 204154127727441507720484051)
      ·
        refine ⟨306231191591162261580726077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204154127727441507720484051 306231191591162261580726077)
        ·
          refine ⟨114836696846685848092772279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 306231191591162261580726077 114836696846685848092772279)
          ·
            refine ⟨172255045270028772139158419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114836696846685848092772279 172255045270028772139158419)
            ·
              refine ⟨258382567905043158208737629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172255045270028772139158419 258382567905043158208737629)
              ·
                refine ⟨96893462964391184328276611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 258382567905043158208737629 96893462964391184328276611)
                ·
                  refine ⟨145340194446586776492414917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96893462964391184328276611 145340194446586776492414917)
                  ·
                    refine ⟨27251286458735020592327797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 145340194446586776492414917 27251286458735020592327797)
                    ·
                      refine ⟨2554808105506408180530731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27251286458735020592327797 2554808105506408180530731)
                      ·
                        rfl

theorem cell23_4975471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 4, 5].length) (baseStart_4975471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4975471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4975471 prefixEnd_4975471 := by exact prefixLift 4975471
  have htrace : WordTrace (prefixWord ++ tailWord_4975471) baseStart_4975471 baseEnd_4975471 := by
    simpa [prefixWord, tailWord_4975471, baseEnd_4975471] using wordTrace_append hprefix tailTrace_4975471
  have hstable : (prefixWord ++ tailWord_4975471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4975471).length < 2 ^ (prefixWord ++ tailWord_4975471).sum := by decide
  have hdescent : baseEnd_4975471 < baseStart_4975471 := by decide
  rcases family_descends (prefixWord ++ tailWord_4975471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4975549 : List Nat := [1, 4, 1, 2, 4, 1, 1, 1, 4, 2, 2]
def baseStart_4975549 : Nat := 118140960795 + 4975549 * 2 ^ 59
def prefixEnd_4975549 : Nat := 4983230072969 + 3 ^ 40 * 4975549 * 2
def baseEnd_4975549 : Nat := 2554848156997458875355373

theorem tailTrace_4975549 : CollatzResearch.WordTrace tailWord_4975549 prefixEnd_4975549 2554848156997458875355373 := by
  unfold tailWord_4975549
  simp only [CollatzResearch.WordTrace]
  refine ⟨181473180651443203961769701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120982120434295469307846467 181473180651443203961769701)
  ·
    refine ⟨34026221372145600742831819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 181473180651443203961769701 34026221372145600742831819)
    ·
      refine ⟨51039332058218401114247729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34026221372145600742831819 51039332058218401114247729)
      ·
        refine ⟨38279499043663800835685797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51039332058218401114247729 38279499043663800835685797)
        ·
          refine ⟨7177406070686962656691087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38279499043663800835685797 7177406070686962656691087)
          ·
            refine ⟨10766109106030443985036631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7177406070686962656691087 10766109106030443985036631)
            ·
              refine ⟨16149163659045665977554947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10766109106030443985036631 16149163659045665977554947)
              ·
                refine ⟨24223745488568498966332421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16149163659045665977554947 24223745488568498966332421)
                ·
                  refine ⟨4541952279106593556187329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24223745488568498966332421 4541952279106593556187329)
                  ·
                    refine ⟨3406464209329945167140497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4541952279106593556187329 3406464209329945167140497)
                    ·
                      refine ⟨2554848156997458875355373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3406464209329945167140497 2554848156997458875355373)
                      ·
                        rfl

theorem cell23_4975549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 4, 2, 2].length) (baseStart_4975549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4975549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4975549 prefixEnd_4975549 := by exact prefixLift 4975549
  have htrace : WordTrace (prefixWord ++ tailWord_4975549) baseStart_4975549 baseEnd_4975549 := by
    simpa [prefixWord, tailWord_4975549, baseEnd_4975549] using wordTrace_append hprefix tailTrace_4975549
  have hstable : (prefixWord ++ tailWord_4975549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4975549).length < 2 ^ (prefixWord ++ tailWord_4975549).sum := by decide
  have hdescent : baseEnd_4975549 < baseStart_4975549 := by decide
  rcases family_descends (prefixWord ++ tailWord_4975549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4975566 : List Nat := [4, 1, 1, 1, 2, 4, 3, 1, 2, 2, 2]
def baseStart_4975566 : Nat := 118140960795 + 4975566 * 2 ^ 59
def prefixEnd_4975566 : Nat := 4983230072969 + 3 ^ 40 * 4975566 * 2
def baseEnd_4975566 : Nat := 2554856886168585308842795

theorem tailTrace_4975566 : CollatzResearch.WordTrace tailWord_4975566 prefixEnd_4975566 2554856886168585308842795 := by
  unfold tailWord_4975566
  simp only [CollatzResearch.WordTrace]
  refine ⟨22684225086547701983142319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120982533794921077243425701 22684225086547701983142319)
  ·
    refine ⟨34026337629821552974713479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22684225086547701983142319 34026337629821552974713479)
    ·
      refine ⟨51039506444732329462070219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34026337629821552974713479 51039506444732329462070219)
      ·
        refine ⟨76559259667098494193105329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51039506444732329462070219 76559259667098494193105329)
        ·
          refine ⟨57419444750323870644828997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76559259667098494193105329 57419444750323870644828997)
          ·
            refine ⟨10766145890685725745905437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57419444750323870644828997 10766145890685725745905437)
            ·
              refine ⟨4037304709007147154714539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10766145890685725745905437 4037304709007147154714539)
              ·
                refine ⟨6055957063510720732071809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4037304709007147154714539 6055957063510720732071809)
                ·
                  refine ⟨4541967797633040549053857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6055957063510720732071809 4541967797633040549053857)
                  ·
                    refine ⟨3406475848224780411790393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4541967797633040549053857 3406475848224780411790393)
                    ·
                      refine ⟨2554856886168585308842795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3406475848224780411790393 2554856886168585308842795)
                      ·
                        rfl

theorem cell23_4975566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 3, 1, 2, 2, 2].length) (baseStart_4975566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4975566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4975566 prefixEnd_4975566 := by exact prefixLift 4975566
  have htrace : WordTrace (prefixWord ++ tailWord_4975566) baseStart_4975566 baseEnd_4975566 := by
    simpa [prefixWord, tailWord_4975566, baseEnd_4975566] using wordTrace_append hprefix tailTrace_4975566
  have hstable : (prefixWord ++ tailWord_4975566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4975566).length < 2 ^ (prefixWord ++ tailWord_4975566).sum := by decide
  have hdescent : baseEnd_4975566 < baseStart_4975566 := by decide
  rcases family_descends (prefixWord ++ tailWord_4975566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4975642 : List Nat := [3, 1, 1, 3, 1, 2, 4, 1, 2, 2, 3]
def baseStart_4975642 : Nat := 118140960795 + 4975642 * 2 ^ 59
def prefixEnd_4975642 : Nat := 4983230072969 + 3 ^ 40 * 4975642 * 2
def baseEnd_4975642 : Nat := 2554895910698327011492445

theorem tailTrace_4975642 : CollatzResearch.WordTrace tailWord_4975642 prefixEnd_4975642 2554895910698327011492445 := by
  unfold tailWord_4975642
  simp only [CollatzResearch.WordTrace]
  refine ⟨45369143160026570211226295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120984381760070853896603453 45369143160026570211226295)
  ·
    refine ⟨68053714740039855316839443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45369143160026570211226295 68053714740039855316839443)
    ·
      refine ⟨102080572110059782975259165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68053714740039855316839443 102080572110059782975259165)
      ·
        refine ⟨38280214541272418615722187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102080572110059782975259165 38280214541272418615722187)
        ·
          refine ⟨57420321811908627923583281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38280214541272418615722187 57420321811908627923583281)
          ·
            refine ⟨43065241358931470942687461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57420321811908627923583281 43065241358931470942687461)
            ·
              refine ⟨8074732754799650801753899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43065241358931470942687461 8074732754799650801753899)
              ·
                refine ⟨12112099132199476202630849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8074732754799650801753899 12112099132199476202630849)
                ·
                  refine ⟨9084074349149607151973137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12112099132199476202630849 9084074349149607151973137)
                  ·
                    refine ⟨6813055761862205363979853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9084074349149607151973137 6813055761862205363979853)
                    ·
                      refine ⟨2554895910698327011492445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6813055761862205363979853 2554895910698327011492445)
                      ·
                        rfl

theorem cell23_4975642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 1, 2, 2, 3].length) (baseStart_4975642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4975642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4975642 prefixEnd_4975642 := by exact prefixLift 4975642
  have htrace : WordTrace (prefixWord ++ tailWord_4975642) baseStart_4975642 baseEnd_4975642 := by
    simpa [prefixWord, tailWord_4975642, baseEnd_4975642] using wordTrace_append hprefix tailTrace_4975642
  have hstable : (prefixWord ++ tailWord_4975642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4975642).length < 2 ^ (prefixWord ++ tailWord_4975642).sum := by decide
  have hdescent : baseEnd_4975642 < baseStart_4975642 := by decide
  rcases family_descends (prefixWord ++ tailWord_4975642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4975662 : List Nat := [4, 1, 3, 1, 1, 1, 4, 2, 6]
def baseStart_4975662 : Nat := 118140960795 + 4975662 * 2 ^ 59
def prefixEnd_4975662 : Nat := 4983230072969 + 3 ^ 40 * 4975662 * 2
def baseEnd_4975662 : Nat := 283878464479046325915817

theorem tailTrace_4975662 : CollatzResearch.WordTrace tailWord_4975662 prefixEnd_4975662 283878464479046325915817 := by
  unfold tailWord_4975662
  simp only [CollatzResearch.WordTrace]
  refine ⟨22684662762504228032579155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120984868066689216173755493 22684662762504228032579155)
  ·
    refine ⟨34026994143756342048868733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22684662762504228032579155 34026994143756342048868733)
    ·
      refine ⟨12760122803908628268325775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34026994143756342048868733 12760122803908628268325775)
      ·
        refine ⟨19140184205862942402488663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12760122803908628268325775 19140184205862942402488663)
        ·
          refine ⟨28710276308794413603732995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19140184205862942402488663 28710276308794413603732995)
          ·
            refine ⟨43065414463191620405599493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28710276308794413603732995 43065414463191620405599493)
            ·
              refine ⟨8074765211848428826049905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43065414463191620405599493 8074765211848428826049905)
              ·
                refine ⟨6056073908886321619537429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8074765211848428826049905 6056073908886321619537429)
                ·
                  refine ⟨283878464479046325915817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6056073908886321619537429 283878464479046325915817)
                  ·
                    rfl

theorem cell23_4975662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 2, 6].length) (baseStart_4975662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4975662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4975662 prefixEnd_4975662 := by exact prefixLift 4975662
  have htrace : WordTrace (prefixWord ++ tailWord_4975662) baseStart_4975662 baseEnd_4975662 := by
    simpa [prefixWord, tailWord_4975662, baseEnd_4975662] using wordTrace_append hprefix tailTrace_4975662
  have hstable : (prefixWord ++ tailWord_4975662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4975662).length < 2 ^ (prefixWord ++ tailWord_4975662).sum := by decide
  have hdescent : baseEnd_4975662 < baseStart_4975662 := by decide
  rcases family_descends (prefixWord ++ tailWord_4975662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4975712 : List Nat := [2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 4]
def baseStart_4975712 : Nat := 118140960795 + 4975712 * 2 ^ 59
def prefixEnd_4975712 : Nat := 4983230072969 + 3 ^ 40 * 4975712 * 2
def baseEnd_4975712 : Nat := 2554931854344141737617123

theorem tailTrace_4975712 : CollatzResearch.WordTrace tailWord_4975712 prefixEnd_4975712 2554931854344141737617123 := by
  unfold tailWord_4975712
  simp only [CollatzResearch.WordTrace]
  refine ⟨90739562874926341399976695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120986083833235121866635593 90739562874926341399976695)
  ·
    refine ⟨136109344312389512099965043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90739562874926341399976695 136109344312389512099965043)
    ·
      refine ⟨204164016468584268149947565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136109344312389512099965043 204164016468584268149947565)
      ·
        refine ⟨76561506175719100556230337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 204164016468584268149947565 76561506175719100556230337)
        ·
          refine ⟨57421129631789325417172753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76561506175719100556230337 57421129631789325417172753)
          ·
            refine ⟨43065847223841994062879565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57421129631789325417172753 43065847223841994062879565)
            ·
              refine ⟨16149692708940747773579837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43065847223841994062879565 16149692708940747773579837)
              ·
                refine ⟨6056134765852780415092439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16149692708940747773579837 6056134765852780415092439)
                ·
                  refine ⟨9084202148779170622638659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6056134765852780415092439 9084202148779170622638659)
                  ·
                    refine ⟨13626303223168755933957989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9084202148779170622638659 13626303223168755933957989)
                    ·
                      refine ⟨2554931854344141737617123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13626303223168755933957989 2554931854344141737617123)
                      ·
                        rfl

theorem cell23_4975712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 4].length) (baseStart_4975712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4975712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4975712 prefixEnd_4975712 := by exact prefixLift 4975712
  have htrace : WordTrace (prefixWord ++ tailWord_4975712) baseStart_4975712 baseEnd_4975712 := by
    simpa [prefixWord, tailWord_4975712, baseEnd_4975712] using wordTrace_append hprefix tailTrace_4975712
  have hstable : (prefixWord ++ tailWord_4975712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4975712).length < 2 ^ (prefixWord ++ tailWord_4975712).sum := by decide
  have hdescent : baseEnd_4975712 < baseStart_4975712 := by decide
  rcases family_descends (prefixWord ++ tailWord_4975712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4975715 : List Nat := [1, 1, 1, 5, 1, 1, 1, 5, 1, 1, 5]
def baseStart_4975715 : Nat := 118140960795 + 4975715 * 2 ^ 59
def prefixEnd_4975715 : Nat := 4983230072969 + 3 ^ 40 * 4975715 * 2
def baseEnd_4975715 : Nat := 2554933394786105225879609

theorem tailTrace_4975715 : CollatzResearch.WordTrace tailWord_4975715 prefixEnd_4975715 2554933394786105225879609 := by
  unfold tailWord_4975715
  simp only [CollatzResearch.WordTrace]
  refine ⟨181479235168841814312312599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120986156779227876208208399 181479235168841814312312599)
  ·
    refine ⟨272218852753262721468468899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181479235168841814312312599 272218852753262721468468899)
    ·
      refine ⟨408328279129894082202703349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272218852753262721468468899 408328279129894082202703349)
      ·
        refine ⟨38280776168427570206503439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 408328279129894082202703349 38280776168427570206503439)
        ·
          refine ⟨57421164252641355309755159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38280776168427570206503439 57421164252641355309755159)
          ·
            refine ⟨86131746378962032964632739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57421164252641355309755159 86131746378962032964632739)
            ·
              refine ⟨129197619568443049446949109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86131746378962032964632739 129197619568443049446949109)
              ·
                refine ⟨12112276834541535885651479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 129197619568443049446949109 12112276834541535885651479)
                ·
                  refine ⟨18168415251812303828477219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12112276834541535885651479 18168415251812303828477219)
                  ·
                    refine ⟨27252622877718455742715829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18168415251812303828477219 27252622877718455742715829)
                    ·
                      refine ⟨2554933394786105225879609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27252622877718455742715829 2554933394786105225879609)
                      ·
                        rfl

theorem cell23_4975715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_4975715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4975715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4975715 prefixEnd_4975715 := by exact prefixLift 4975715
  have htrace : WordTrace (prefixWord ++ tailWord_4975715) baseStart_4975715 baseEnd_4975715 := by
    simpa [prefixWord, tailWord_4975715, baseEnd_4975715] using wordTrace_append hprefix tailTrace_4975715
  have hstable : (prefixWord ++ tailWord_4975715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4975715).length < 2 ^ (prefixWord ++ tailWord_4975715).sum := by decide
  have hdescent : baseEnd_4975715 < baseStart_4975715 := by decide
  rcases family_descends (prefixWord ++ tailWord_4975715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4975752 : List Nat := [2, 1, 3, 4, 2, 1, 1, 9]
def baseStart_4975752 : Nat := 118140960795 + 4975752 * 2 ^ 59
def prefixEnd_4975752 : Nat := 4983230072969 + 3 ^ 40 * 4975752 * 2
def baseEnd_4975752 : Nat := 94627866428530428930257

theorem tailTrace_4975752 : CollatzResearch.WordTrace tailWord_4975752 prefixEnd_4975752 94627866428530428930257 := by
  unfold tailWord_4975752
  simp only [CollatzResearch.WordTrace]
  refine ⟨90740292334853884815704755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120987056446471846420939673 90740292334853884815704755)
  ·
    refine ⟨136110438502280827223557133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90740292334853884815704755 136110438502280827223557133)
    ·
      refine ⟨51041414438355310208833925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136110438502280827223557133 51041414438355310208833925)
      ·
        refine ⟨9570265207191620664156361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51041414438355310208833925 9570265207191620664156361)
        ·
          refine ⟨7177698905393715498117271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9570265207191620664156361 7177698905393715498117271)
          ·
            refine ⟨10766548358090573247175907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7177698905393715498117271 10766548358090573247175907)
            ·
              refine ⟨16149822537135859870763861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10766548358090573247175907 16149822537135859870763861)
              ·
                refine ⟨94627866428530428930257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16149822537135859870763861 94627866428530428930257)
                ·
                  rfl

theorem cell23_4975752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 9].length) (baseStart_4975752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4975752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4975752 prefixEnd_4975752 := by exact prefixLift 4975752
  have htrace : WordTrace (prefixWord ++ tailWord_4975752) baseStart_4975752 baseEnd_4975752 := by
    simpa [prefixWord, tailWord_4975752, baseEnd_4975752] using wordTrace_append hprefix tailTrace_4975752
  have hstable : (prefixWord ++ tailWord_4975752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4975752).length < 2 ^ (prefixWord ++ tailWord_4975752).sum := by decide
  have hdescent : baseEnd_4975752 < baseStart_4975752 := by decide
  rcases family_descends (prefixWord ++ tailWord_4975752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4975780 : List Nat := [2, 3, 1, 2, 3, 2, 3, 2, 1, 2, 2]
def baseStart_4975780 : Nat := 118140960795 + 4975780 * 2 ^ 59
def prefixEnd_4975780 : Nat := 4983230072969 + 3 ^ 40 * 4975780 * 2
def baseEnd_4975780 : Nat := 2554966771028647471566811

theorem tailTrace_4975780 : CollatzResearch.WordTrace tailWord_4975780 prefixEnd_4975780 2554966771028647471566811 := by
  unfold tailWord_4975780
  simp only [CollatzResearch.WordTrace]
  refine ⟨90740802956803165206714397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120987737275737553608952529 90740802956803165206714397)
  ·
    refine ⟨34027801108801186952517899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90740802956803165206714397 34027801108801186952517899)
    ·
      refine ⟨51041701663201780428776849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34027801108801186952517899 51041701663201780428776849)
      ·
        refine ⟨38281276247401335321582637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51041701663201780428776849 38281276247401335321582637)
        ·
          refine ⟨14355478592775500745593489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38281276247401335321582637 14355478592775500745593489)
          ·
            refine ⟨10766608944581625559195117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14355478592775500745593489 10766608944581625559195117)
            ·
              refine ⟨4037478354218109584698169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10766608944581625559195117 4037478354218109584698169)
              ·
                refine ⟨3028108765663582188523627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4037478354218109584698169 3028108765663582188523627)
                ·
                  refine ⟨4542163148495373282785441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3028108765663582188523627 4542163148495373282785441)
                  ·
                    refine ⟨3406622361371529962089081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4542163148495373282785441 3406622361371529962089081)
                    ·
                      refine ⟨2554966771028647471566811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3406622361371529962089081 2554966771028647471566811)
                      ·
                        rfl

theorem cell23_4975780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 3, 2, 1, 2, 2].length) (baseStart_4975780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4975780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4975780 prefixEnd_4975780 := by exact prefixLift 4975780
  have htrace : WordTrace (prefixWord ++ tailWord_4975780) baseStart_4975780 baseEnd_4975780 := by
    simpa [prefixWord, tailWord_4975780, baseEnd_4975780] using wordTrace_append hprefix tailTrace_4975780
  have hstable : (prefixWord ++ tailWord_4975780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4975780).length < 2 ^ (prefixWord ++ tailWord_4975780).sum := by decide
  have hdescent : baseEnd_4975780 < baseStart_4975780 := by decide
  rcases family_descends (prefixWord ++ tailWord_4975780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4975795 : List Nat := [1, 1, 1, 2, 3, 2, 2, 3, 2, 6]
def baseStart_4975795 : Nat := 118140960795 + 4975795 * 2 ^ 59
def prefixEnd_4975795 : Nat := 4983230072969 + 3 ^ 40 * 4975795 * 2
def baseEnd_4975795 : Nat := 851658157746154970959747

theorem tailTrace_4975795 : CollatzResearch.WordTrace tailWord_4975795 prefixEnd_4975795 851658157746154970959747 := by
  unfold tailWord_4975795
  simp only [CollatzResearch.WordTrace]
  refine ⟨181482153008551987975224839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120988102005701325316816559 181482153008551987975224839)
  ·
    refine ⟨272223229512827981962837259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181482153008551987975224839 272223229512827981962837259)
    ·
      refine ⟨408334844269241972944255889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272223229512827981962837259 408334844269241972944255889)
      ·
        refine ⟨306251133201931479708191917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 408334844269241972944255889 306251133201931479708191917)
        ·
          refine ⟨114844174950724304890571969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 306251133201931479708191917 114844174950724304890571969)
          ·
            refine ⟨86133131213043228667928977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114844174950724304890571969 86133131213043228667928977)
            ·
              refine ⟨64599848409782421500946733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86133131213043228667928977 64599848409782421500946733)
              ·
                refine ⟨24224943153668408062855025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64599848409782421500946733 24224943153668408062855025)
                ·
                  refine ⟨18168707365251306047141269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24224943153668408062855025 18168707365251306047141269)
                  ·
                    refine ⟨851658157746154970959747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18168707365251306047141269 851658157746154970959747)
                    ·
                      rfl

theorem cell23_4975795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 2, 6].length) (baseStart_4975795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4975795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4975795 prefixEnd_4975795 := by exact prefixLift 4975795
  have htrace : WordTrace (prefixWord ++ tailWord_4975795) baseStart_4975795 baseEnd_4975795 := by
    simpa [prefixWord, tailWord_4975795, baseEnd_4975795] using wordTrace_append hprefix tailTrace_4975795
  have hstable : (prefixWord ++ tailWord_4975795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4975795).length < 2 ^ (prefixWord ++ tailWord_4975795).sum := by decide
  have hdescent : baseEnd_4975795 < baseStart_4975795 := by decide
  rcases family_descends (prefixWord ++ tailWord_4975795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4975806 : List Nat := [4, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2]
def baseStart_4975806 : Nat := 118140960795 + 4975806 * 2 ^ 59
def prefixEnd_4975806 : Nat := 4983230072969 + 3 ^ 40 * 4975806 * 2
def baseEnd_4975806 : Nat := 2554980121525664369841691

theorem tailTrace_4975806 : CollatzResearch.WordTrace tailWord_4975806 prefixEnd_4975806 2554980121525664369841691 := by
  unfold tailWord_4975806
  simp only [CollatzResearch.WordTrace]
  refine ⟨22685319276439017106734409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120988369474341424569250181 22685319276439017106734409)
  ·
    refine ⟨17013989457329262830050807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22685319276439017106734409 17013989457329262830050807)
    ·
      refine ⟨25520984185993894245076211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17013989457329262830050807 25520984185993894245076211)
      ·
        refine ⟨38281476278990841367614317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25520984185993894245076211 38281476278990841367614317)
        ·
          refine ⟨14355553604621565512855369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38281476278990841367614317 14355553604621565512855369)
          ·
            refine ⟨10766665203466174134641527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14355553604621565512855369 10766665203466174134641527)
            ·
              refine ⟨16149997805199261201962291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10766665203466174134641527 16149997805199261201962291)
              ·
                refine ⟨24224996707798891802943437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16149997805199261201962291 24224996707798891802943437)
                ·
                  refine ⟨9084373765424584426103789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24224996707798891802943437 9084373765424584426103789)
                  ·
                    refine ⟨3406640162034219159788921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9084373765424584426103789 3406640162034219159788921)
                    ·
                      refine ⟨2554980121525664369841691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3406640162034219159788921 2554980121525664369841691)
                      ·
                        rfl

theorem cell23_4975806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2].length) (baseStart_4975806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4975806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4975806 prefixEnd_4975806 := by exact prefixLift 4975806
  have htrace : WordTrace (prefixWord ++ tailWord_4975806) baseStart_4975806 baseEnd_4975806 := by
    simpa [prefixWord, tailWord_4975806, baseEnd_4975806] using wordTrace_append hprefix tailTrace_4975806
  have hstable : (prefixWord ++ tailWord_4975806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4975806).length < 2 ^ (prefixWord ++ tailWord_4975806).sum := by decide
  have hdescent : baseEnd_4975806 < baseStart_4975806 := by decide
  rcases family_descends (prefixWord ++ tailWord_4975806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4975819 : List Nat := [1, 1, 1, 1, 3, 2, 2, 4, 4, 2, 2]
def baseStart_4975819 : Nat := 118140960795 + 4975819 * 2 ^ 59
def prefixEnd_4975819 : Nat := 4983230072969 + 3 ^ 40 * 4975819 * 2
def baseEnd_4975819 : Nat := 2554986796774172818979131

theorem tailTrace_4975819 : CollatzResearch.WordTrace tailWord_4975819 prefixEnd_4975819 2554986796774172818979131 := by
  unfold tailWord_4975819
  simp only [CollatzResearch.WordTrace]
  refine ⟨181483028360465040074098511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120988685573643360049399007 181483028360465040074098511)
  ·
    refine ⟨272224542540697560111147767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181483028360465040074098511 272224542540697560111147767)
    ·
      refine ⟨408336813811046340166721651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272224542540697560111147767 408336813811046340166721651)
      ·
        refine ⟨612505220716569510250082477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 408336813811046340166721651 612505220716569510250082477)
        ·
          refine ⟨229689457768713566343780929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 612505220716569510250082477 229689457768713566343780929)
          ·
            refine ⟨172267093326535174757835697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 229689457768713566343780929 172267093326535174757835697)
            ·
              refine ⟨129200319994901381068376773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 172267093326535174757835697 129200319994901381068376773)
              ·
                refine ⟨24225059999044008950320645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 129200319994901381068376773 24225059999044008950320645)
                ·
                  refine ⟨4542198749820751678185121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24225059999044008950320645 4542198749820751678185121)
                  ·
                    refine ⟨3406649062365563758638841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4542198749820751678185121 3406649062365563758638841)
                    ·
                      refine ⟨2554986796774172818979131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3406649062365563758638841 2554986796774172818979131)
                      ·
                        rfl

theorem cell23_4975819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 4, 2, 2].length) (baseStart_4975819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4975819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4975819 prefixEnd_4975819 := by exact prefixLift 4975819
  have htrace : WordTrace (prefixWord ++ tailWord_4975819) baseStart_4975819 baseEnd_4975819 := by
    simpa [prefixWord, tailWord_4975819, baseEnd_4975819] using wordTrace_append hprefix tailTrace_4975819
  have hstable : (prefixWord ++ tailWord_4975819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4975819).length < 2 ^ (prefixWord ++ tailWord_4975819).sum := by decide
  have hdescent : baseEnd_4975819 < baseStart_4975819 := by decide
  rcases family_descends (prefixWord ++ tailWord_4975819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4975830 : List Nat := [5, 2, 1, 2, 2, 1, 2, 2, 2, 1, 3]
def baseStart_4975830 : Nat := 118140960795 + 4975830 * 2 ^ 59
def prefixEnd_4975830 : Nat := 4983230072969 + 3 ^ 40 * 4975830 * 2
def baseEnd_4975830 : Nat := 2554992445061372275941581

theorem tailTrace_4975830 : CollatzResearch.WordTrace tailWord_4975830 prefixEnd_4975830 2554992445061372275941581 := by
  unfold tailWord_4975830
  simp only [CollatzResearch.WordTrace]
  refine ⟨11342714347714074309546809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 120988953042283459301832629 11342714347714074309546809)
  ·
    refine ⟨8507035760785555732160107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11342714347714074309546809 8507035760785555732160107)
    ·
      refine ⟨12760553641178333598240161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8507035760785555732160107 12760553641178333598240161)
      ·
        refine ⟨9570415230883750198680121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12760553641178333598240161 9570415230883750198680121)
        ·
          refine ⟨7177811423162812649010091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9570415230883750198680121 7177811423162812649010091)
          ·
            refine ⟨10766717134744218973515137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7177811423162812649010091 10766717134744218973515137)
            ·
              refine ⟨8075037851058164230136353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10766717134744218973515137 8075037851058164230136353)
              ·
                refine ⟨6056278388293623172602265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8075037851058164230136353 6056278388293623172602265)
                ·
                  refine ⟨4542208791220217379451699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6056278388293623172602265 4542208791220217379451699)
                  ·
                    refine ⟨6813313186830326069177549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4542208791220217379451699 6813313186830326069177549)
                    ·
                      refine ⟨2554992445061372275941581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6813313186830326069177549 2554992445061372275941581)
                      ·
                        rfl

theorem cell23_4975830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_4975830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4975830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4975830 prefixEnd_4975830 := by exact prefixLift 4975830
  have htrace : WordTrace (prefixWord ++ tailWord_4975830) baseStart_4975830 baseEnd_4975830 := by
    simpa [prefixWord, tailWord_4975830, baseEnd_4975830] using wordTrace_append hprefix tailTrace_4975830
  have hstable : (prefixWord ++ tailWord_4975830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4975830).length < 2 ^ (prefixWord ++ tailWord_4975830).sum := by decide
  have hdescent : baseEnd_4975830 < baseStart_4975830 := by decide
  rcases family_descends (prefixWord ++ tailWord_4975830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4975852 : List Nat := [2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 3]
def baseStart_4975852 : Nat := 118140960795 + 4975852 * 2 ^ 59
def prefixEnd_4975852 : Nat := 4983230072969 + 3 ^ 40 * 4975852 * 2
def baseEnd_4975852 : Nat := 2555003741635771189866479

theorem tailTrace_4975852 : CollatzResearch.WordTrace tailWord_4975852 prefixEnd_4975852 2555003741635771189866479 := by
  unfold tailWord_4975852
  simp only [CollatzResearch.WordTrace]
  refine ⟨90742115984672743355024905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120989487979563657806699873 90742115984672743355024905)
  ·
    refine ⟨68056586988504557516268679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90742115984672743355024905 68056586988504557516268679)
    ·
      refine ⟨102084880482756836274403019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68056586988504557516268679 102084880482756836274403019)
      ·
        refine ⟨153127320724135254411604529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102084880482756836274403019 153127320724135254411604529)
        ·
          refine ⟨114845490543101440808703397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153127320724135254411604529 114845490543101440808703397)
          ·
            refine ⟨21533529476831520151631887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 114845490543101440808703397 21533529476831520151631887)
            ·
              refine ⟨32300294215247280227447831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21533529476831520151631887 32300294215247280227447831)
              ·
                refine ⟨48450441322870920341171747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32300294215247280227447831 48450441322870920341171747)
                ·
                  refine ⟨72675661984306380511757621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48450441322870920341171747 72675661984306380511757621)
                  ·
                    refine ⟨6813343311028723172977277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 72675661984306380511757621 6813343311028723172977277)
                    ·
                      refine ⟨2555003741635771189866479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6813343311028723172977277 2555003741635771189866479)
                      ·
                        rfl

theorem cell23_4975852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 3].length) (baseStart_4975852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4975852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4975852 prefixEnd_4975852 := by exact prefixLift 4975852
  have htrace : WordTrace (prefixWord ++ tailWord_4975852) baseStart_4975852 baseEnd_4975852 := by
    simpa [prefixWord, tailWord_4975852, baseEnd_4975852] using wordTrace_append hprefix tailTrace_4975852
  have hstable : (prefixWord ++ tailWord_4975852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4975852).length < 2 ^ (prefixWord ++ tailWord_4975852).sum := by decide
  have hdescent : baseEnd_4975852 < baseStart_4975852 := by decide
  rcases family_descends (prefixWord ++ tailWord_4975852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4975853 : List Nat := [1, 5, 1, 2, 2, 1, 2, 3, 2, 2, 2]
def baseStart_4975853 : Nat := 118140960795 + 4975853 * 2 ^ 59
def prefixEnd_4975853 : Nat := 4983230072969 + 3 ^ 40 * 4975853 * 2
def baseEnd_4975853 : Nat := 2555004255116425685953975

theorem tailTrace_4975853 : CollatzResearch.WordTrace tailWord_4975853 prefixEnd_4975853 2555004255116425685953975 := by
  unfold tailWord_4975853
  simp only [CollatzResearch.WordTrace]
  refine ⟨181484268442341863880836213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120989512294894575920557475 181484268442341863880836213)
  ·
    refine ⟨17014150166469549738828395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 181484268442341863880836213 17014150166469549738828395)
    ·
      refine ⟨25521225249704324608242593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17014150166469549738828395 25521225249704324608242593)
      ·
        refine ⟨19140918937278243456181945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25521225249704324608242593 19140918937278243456181945)
        ·
          refine ⟨14355689202958682592136459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19140918937278243456181945 14355689202958682592136459)
          ·
            refine ⟨21533533804438023888204689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14355689202958682592136459 21533533804438023888204689)
            ·
              refine ⟨16150150353328517916153517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21533533804438023888204689 16150150353328517916153517)
              ·
                refine ⟨6056306382498194218557569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16150150353328517916153517 6056306382498194218557569)
                ·
                  refine ⟨4542229786873645663918177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6056306382498194218557569 4542229786873645663918177)
                  ·
                    refine ⟨3406672340155234247938633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4542229786873645663918177 3406672340155234247938633)
                    ·
                      refine ⟨2555004255116425685953975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3406672340155234247938633 2555004255116425685953975)
                      ·
                        rfl

theorem cell23_4975853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 3, 2, 2, 2].length) (baseStart_4975853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4975853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4975853 prefixEnd_4975853 := by exact prefixLift 4975853
  have htrace : WordTrace (prefixWord ++ tailWord_4975853) baseStart_4975853 baseEnd_4975853 := by
    simpa [prefixWord, tailWord_4975853, baseEnd_4975853] using wordTrace_append hprefix tailTrace_4975853
  have hstable : (prefixWord ++ tailWord_4975853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4975853).length < 2 ^ (prefixWord ++ tailWord_4975853).sum := by decide
  have hdescent : baseEnd_4975853 < baseStart_4975853 := by decide
  rcases family_descends (prefixWord ++ tailWord_4975853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4975876 : List Nat := [2, 3, 2, 2, 2, 2, 2, 3, 5]
def baseStart_4975876 : Nat := 118140960795 + 4975876 * 2 ^ 59
def prefixEnd_4975876 : Nat := 4983230072969 + 3 ^ 40 * 4975876 * 2
def baseEnd_4975876 : Nat := 283890673907942121774041

theorem tailTrace_4975876 : CollatzResearch.WordTrace tailWord_4975876 prefixEnd_4975876 283890673907942121774041 := by
  unfold tailWord_4975876
  simp only [CollatzResearch.WordTrace]
  refine ⟨90742553660629269404461741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120990071547505692539282321 90742553660629269404461741)
  ·
    refine ⟨34028457622735976026673153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90742553660629269404461741 34028457622735976026673153)
    ·
      refine ⟨25521343217051982020004865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34028457622735976026673153 25521343217051982020004865)
      ·
        refine ⟨19141007412788986515003649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25521343217051982020004865 19141007412788986515003649)
        ·
          refine ⟨14355755559591739886252737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19141007412788986515003649 14355755559591739886252737)
          ·
            refine ⟨10766816669693804914689553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14355755559591739886252737 10766816669693804914689553)
            ·
              refine ⟨8075112502270353686017165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10766816669693804914689553 8075112502270353686017165)
              ·
                refine ⟨3028167188351382632256437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8075112502270353686017165 3028167188351382632256437)
                ·
                  refine ⟨283890673907942121774041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3028167188351382632256437 283890673907942121774041)
                  ·
                    rfl

theorem cell23_4975876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 3, 5].length) (baseStart_4975876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4975876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4975876 prefixEnd_4975876 := by exact prefixLift 4975876
  have htrace : WordTrace (prefixWord ++ tailWord_4975876) baseStart_4975876 baseEnd_4975876 := by
    simpa [prefixWord, tailWord_4975876, baseEnd_4975876] using wordTrace_append hprefix tailTrace_4975876
  have hstable : (prefixWord ++ tailWord_4975876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4975876).length < 2 ^ (prefixWord ++ tailWord_4975876).sum := by decide
  have hdescent : baseEnd_4975876 < baseStart_4975876 := by decide
  rcases family_descends (prefixWord ++ tailWord_4975876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4975932 : List Nat := [2, 2, 2, 2, 1, 3, 1, 2, 8]
def baseStart_4975932 : Nat := 118140960795 + 4975932 * 2 ^ 59
def prefixEnd_4975932 : Nat := 4983230072969 + 3 ^ 40 * 4975932 * 2
def baseEnd_4975932 : Nat := 283893868898681208540679

theorem tailTrace_4975932 : CollatzResearch.WordTrace tailWord_4975932 prefixEnd_4975932 283893868898681208540679 := by
  unfold tailWord_4975932
  simp only [CollatzResearch.WordTrace]
  refine ⟨90743574904527830186481025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120991433206037106915308033 90743574904527830186481025)
  ·
    refine ⟨68057681178395872639860769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90743574904527830186481025 68057681178395872639860769)
    ·
      refine ⟨51043260883796904479895577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68057681178395872639860769 51043260883796904479895577)
      ·
        refine ⟨38282445662847678359921683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51043260883796904479895577 38282445662847678359921683)
        ·
          refine ⟨57423668494271517539882525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38282445662847678359921683 57423668494271517539882525)
          ·
            refine ⟨21533875685351819077455947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57423668494271517539882525 21533875685351819077455947)
            ·
              refine ⟨32300813528027728616183921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21533875685351819077455947 32300813528027728616183921)
              ·
                refine ⟨24225610146020796462137941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32300813528027728616183921 24225610146020796462137941)
                ·
                  refine ⟨283893868898681208540679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24225610146020796462137941 283893868898681208540679)
                  ·
                    rfl

theorem cell23_4975932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 8].length) (baseStart_4975932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4975932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4975932 prefixEnd_4975932 := by exact prefixLift 4975932
  have htrace : WordTrace (prefixWord ++ tailWord_4975932) baseStart_4975932 baseEnd_4975932 := by
    simpa [prefixWord, tailWord_4975932, baseEnd_4975932] using wordTrace_append hprefix tailTrace_4975932
  have hstable : (prefixWord ++ tailWord_4975932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4975932).length < 2 ^ (prefixWord ++ tailWord_4975932).sum := by decide
  have hdescent : baseEnd_4975932 < baseStart_4975932 := by decide
  rcases family_descends (prefixWord ++ tailWord_4975932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4975953 : List Nat := [1, 2, 2, 1, 4, 1, 5, 2, 1, 4]
def baseStart_4975953 : Nat := 118140960795 + 4975953 * 2 ^ 59
def prefixEnd_4975953 : Nat := 4983230072969 + 3 ^ 40 * 4975953 * 2
def baseEnd_4975953 : Nat := 851685201060625098234505

theorem tailTrace_4975953 : CollatzResearch.WordTrace tailWord_4975953 prefixEnd_4975953 851685201060625098234505 := by
  unfold tailWord_4975953
  simp only [CollatzResearch.WordTrace]
  refine ⟨181487915741979580959476513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120991943827986387306317675 181487915741979580959476513)
  ·
    refine ⟨136115936806484685719607385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181487915741979580959476513 136115936806484685719607385)
    ·
      refine ⟨102086952604863514289705539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136115936806484685719607385 102086952604863514289705539)
      ·
        refine ⟨153130428907295271434558309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102086952604863514289705539 153130428907295271434558309)
        ·
          refine ⟨28711955420117863393979683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 153130428907295271434558309 28711955420117863393979683)
          ·
            refine ⟨43067933130176795090969525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28711955420117863393979683 43067933130176795090969525)
            ·
              refine ⟨4037618730954074539778393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43067933130176795090969525 4037618730954074539778393)
              ·
                refine ⟨3028214048215555904833795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4037618730954074539778393 3028214048215555904833795)
                ·
                  refine ⟨4542321072323333857250693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3028214048215555904833795 4542321072323333857250693)
                  ·
                    refine ⟨851685201060625098234505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4542321072323333857250693 851685201060625098234505)
                    ·
                      rfl

theorem cell23_4975953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 5, 2, 1, 4].length) (baseStart_4975953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4975953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4975953 prefixEnd_4975953 := by exact prefixLift 4975953
  have htrace : WordTrace (prefixWord ++ tailWord_4975953) baseStart_4975953 baseEnd_4975953 := by
    simpa [prefixWord, tailWord_4975953, baseEnd_4975953] using wordTrace_append hprefix tailTrace_4975953
  have hstable : (prefixWord ++ tailWord_4975953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4975953).length < 2 ^ (prefixWord ++ tailWord_4975953).sum := by decide
  have hdescent : baseEnd_4975953 < baseStart_4975953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4975953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4975969 : List Nat := [1, 2, 3, 1, 1, 1, 1, 3, 3, 5, 2]
def baseStart_4975969 : Nat := 118140960795 + 4975969 * 2 ^ 59
def prefixEnd_4975969 : Nat := 4983230072969 + 3 ^ 40 * 4975969 * 2
def baseEnd_4975969 : Nat := 2555063818872347232103441

theorem tailTrace_4975969 : CollatzResearch.WordTrace tailWord_4975969 prefixEnd_4975969 2555063818872347232103441 := by
  unfold tailWord_4975969
  simp only [CollatzResearch.WordTrace]
  refine ⟨181488499309921615692058961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120992332873281077128039307 181488499309921615692058961)
  ·
    refine ⟨136116374482441211769044221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181488499309921615692058961 136116374482441211769044221)
    ·
      refine ⟨51043640430915454413391583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136116374482441211769044221 51043640430915454413391583)
      ·
        refine ⟨76565460646373181620087375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51043640430915454413391583 76565460646373181620087375)
        ·
          refine ⟨114848190969559772430131063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76565460646373181620087375 114848190969559772430131063)
          ·
            refine ⟨172272286454339658645196595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114848190969559772430131063 172272286454339658645196595)
            ·
              refine ⟨258408429681509487967794893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172272286454339658645196595 258408429681509487967794893)
              ·
                refine ⟨96903161130566057987923085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 258408429681509487967794893 96903161130566057987923085)
                ·
                  refine ⟨36338685423962271745471157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96903161130566057987923085 36338685423962271745471157)
                  ·
                    refine ⟨3406751758496462976137921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36338685423962271745471157 3406751758496462976137921)
                    ·
                      refine ⟨2555063818872347232103441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3406751758496462976137921 2555063818872347232103441)
                      ·
                        rfl

theorem cell23_4975969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 5, 2].length) (baseStart_4975969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4975969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4975969 prefixEnd_4975969 := by exact prefixLift 4975969
  have htrace : WordTrace (prefixWord ++ tailWord_4975969) baseStart_4975969 baseEnd_4975969 := by
    simpa [prefixWord, tailWord_4975969, baseEnd_4975969] using wordTrace_append hprefix tailTrace_4975969
  have hstable : (prefixWord ++ tailWord_4975969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4975969).length < 2 ^ (prefixWord ++ tailWord_4975969).sum := by decide
  have hdescent : baseEnd_4975969 < baseStart_4975969 := by decide
  rcases family_descends (prefixWord ++ tailWord_4975969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4975996 : List Nat := [2, 2, 2, 1, 1, 1, 7, 1, 1, 5]
def baseStart_4975996 : Nat := 118140960795 + 4975996 * 2 ^ 59
def prefixEnd_4975996 : Nat := 4983230072969 + 3 ^ 40 * 4975996 * 2
def baseEnd_4975996 : Nat := 851692560950006208821939

theorem tailTrace_4975996 : CollatzResearch.WordTrace tailWord_4975996 prefixEnd_4975996 851692560950006208821939 := by
  unfold tailWord_4975996
  simp only [CollatzResearch.WordTrace]
  refine ⟨90744742040411899651645921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120992989387215866202194561 90744742040411899651645921)
  ·
    refine ⟨68058556530308924738734441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90744742040411899651645921 68058556530308924738734441)
    ·
      refine ⟨51043917397731693554050831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68058556530308924738734441 51043917397731693554050831)
      ·
        refine ⟨76565876096597540331076247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51043917397731693554050831 76565876096597540331076247)
        ·
          refine ⟨114848814144896310496614371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76565876096597540331076247 114848814144896310496614371)
          ·
            refine ⟨172273221217344465744921557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114848814144896310496614371 172273221217344465744921557)
            ·
              refine ⟨4037653622281510915896599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 172273221217344465744921557 4037653622281510915896599)
              ·
                refine ⟨6056480433422266373844899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4037653622281510915896599 6056480433422266373844899)
                ·
                  refine ⟨9084720650133399560767349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6056480433422266373844899 9084720650133399560767349)
                  ·
                    refine ⟨851692560950006208821939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9084720650133399560767349 851692560950006208821939)
                    ·
                      rfl

theorem cell23_4975996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 7, 1, 1, 5].length) (baseStart_4975996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4975996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4975996 prefixEnd_4975996 := by exact prefixLift 4975996
  have htrace : WordTrace (prefixWord ++ tailWord_4975996) baseStart_4975996 baseEnd_4975996 := by
    simpa [prefixWord, tailWord_4975996, baseEnd_4975996] using wordTrace_append hprefix tailTrace_4975996
  have hstable : (prefixWord ++ tailWord_4975996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4975996).length < 2 ^ (prefixWord ++ tailWord_4975996).sum := by decide
  have hdescent : baseEnd_4975996 < baseStart_4975996 := by decide
  rcases family_descends (prefixWord ++ tailWord_4975996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4976026 : List Nat := [3, 1, 1, 4, 1, 1, 1, 5, 2, 4]
def baseStart_4976026 : Nat := 118140960795 + 4976026 * 2 ^ 59
def prefixEnd_4976026 : Nat := 4983230072969 + 3 ^ 40 * 4976026 * 2
def baseEnd_4976026 : Nat := 851697695756551169696893

theorem tailTrace_4976026 : CollatzResearch.WordTrace tailWord_4976026 prefixEnd_4976026 851697695756551169696893 := by
  unfold tailWord_4976026
  simp only [CollatzResearch.WordTrace]
  refine ⟨45372644567678778606720983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120993718847143409617922621 45372644567678778606720983)
  ·
    refine ⟨68058966851518167910081475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45372644567678778606720983 68058966851518167910081475)
    ·
      refine ⟨102088450277277251865122213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68058966851518167910081475 102088450277277251865122213)
      ·
        refine ⟨19141584426989484724710415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102088450277277251865122213 19141584426989484724710415)
        ·
          refine ⟨28712376640484227087065623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19141584426989484724710415 28712376640484227087065623)
          ·
            refine ⟨43068564960726340630598435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28712376640484227087065623 43068564960726340630598435)
            ·
              refine ⟨64602847441089510945897653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43068564960726340630598435 64602847441089510945897653)
              ·
                refine ⟨6056516947602141651177905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 64602847441089510945897653 6056516947602141651177905)
                ·
                  refine ⟨4542387710701606238383429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6056516947602141651177905 4542387710701606238383429)
                  ·
                    refine ⟨851697695756551169696893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4542387710701606238383429 851697695756551169696893)
                    ·
                      rfl

theorem cell23_4976026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 5, 2, 4].length) (baseStart_4976026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4976026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4976026 prefixEnd_4976026 := by exact prefixLift 4976026
  have htrace : WordTrace (prefixWord ++ tailWord_4976026) baseStart_4976026 baseEnd_4976026 := by
    simpa [prefixWord, tailWord_4976026, baseEnd_4976026] using wordTrace_append hprefix tailTrace_4976026
  have hstable : (prefixWord ++ tailWord_4976026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4976026).length < 2 ^ (prefixWord ++ tailWord_4976026).sum := by decide
  have hdescent : baseEnd_4976026 < baseStart_4976026 := by decide
  rcases family_descends (prefixWord ++ tailWord_4976026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4976036 : List Nat := [2, 3, 1, 2, 1, 1, 1, 6, 1, 2, 3]
def baseStart_4976036 : Nat := 118140960795 + 4976036 * 2 ^ 59
def prefixEnd_4976036 : Nat := 4983230072969 + 3 ^ 40 * 4976036 * 2
def baseEnd_4976036 : Nat := 2555098222076198469965633

theorem tailTrace_4976036 : CollatzResearch.WordTrace tailWord_4976036 prefixEnd_4976036 2555098222076198469965633 := by
  unfold tailWord_4976036
  simp only [CollatzResearch.WordTrace]
  refine ⟨90745471500339443067373981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120993962000452590756498641 90745471500339443067373981)
  ·
    refine ⟨34029551812627291150265243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90745471500339443067373981 34029551812627291150265243)
    ·
      refine ⟨51044327718940936725397865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34029551812627291150265243 51044327718940936725397865)
      ·
        refine ⟨38283245789205702544048399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51044327718940936725397865 38283245789205702544048399)
        ·
          refine ⟨57424868683808553816072599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38283245789205702544048399 57424868683808553816072599)
          ·
            refine ⟨86137303025712830724108899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57424868683808553816072599 86137303025712830724108899)
            ·
              refine ⟨129205954538569246086163349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86137303025712830724108899 129205954538569246086163349)
              ·
                refine ⟨6056529118995433410288907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 129205954538569246086163349 6056529118995433410288907)
                ·
                  refine ⟨9084793678493150115433361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6056529118995433410288907 9084793678493150115433361)
                  ·
                    refine ⟨6813595258869862586575021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9084793678493150115433361 6813595258869862586575021)
                    ·
                      refine ⟨2555098222076198469965633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6813595258869862586575021 2555098222076198469965633)
                      ·
                        rfl

theorem cell23_4976036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 6, 1, 2, 3].length) (baseStart_4976036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4976036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4976036 prefixEnd_4976036 := by exact prefixLift 4976036
  have htrace : WordTrace (prefixWord ++ tailWord_4976036) baseStart_4976036 baseEnd_4976036 := by
    simpa [prefixWord, tailWord_4976036, baseEnd_4976036] using wordTrace_append hprefix tailTrace_4976036
  have hstable : (prefixWord ++ tailWord_4976036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4976036).length < 2 ^ (prefixWord ++ tailWord_4976036).sum := by decide
  have hdescent : baseEnd_4976036 < baseStart_4976036 := by decide
  rcases family_descends (prefixWord ++ tailWord_4976036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4976053 : List Nat := [1, 3, 3, 2, 2, 2, 1, 3, 1, 2, 3]
def baseStart_4976053 : Nat := 118140960795 + 4976053 * 2 ^ 59
def prefixEnd_4976053 : Nat := 4983230072969 + 3 ^ 40 * 4976053 * 2
def baseEnd_4976053 : Nat := 2555106951247324903453055

theorem tailTrace_4976053 : CollatzResearch.WordTrace tailWord_4976053 prefixEnd_4976053 2555106951247324903453055 := by
  unfold tailWord_4976053
  simp only [CollatzResearch.WordTrace]
  refine ⟨181491563041617298038116813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120994375361078198692077875 181491563041617298038116813)
  ·
    refine ⟨68059336140606486764293805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181491563041617298038116813 68059336140606486764293805)
    ·
      refine ⟨25522251052727432536610177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68059336140606486764293805 25522251052727432536610177)
      ·
        refine ⟨19141688289545574402457633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25522251052727432536610177 19141688289545574402457633)
        ·
          refine ⟨14356266217159180801843225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19141688289545574402457633 14356266217159180801843225)
          ·
            refine ⟨10767199662869385601382419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14356266217159180801843225 10767199662869385601382419)
            ·
              refine ⟨16150799494304078402073629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10767199662869385601382419 16150799494304078402073629)
              ·
                refine ⟨6056549810364029400777611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16150799494304078402073629 6056549810364029400777611)
                ·
                  refine ⟨9084824715546044101166417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6056549810364029400777611 9084824715546044101166417)
                  ·
                    refine ⟨6813618536659533075874813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9084824715546044101166417 6813618536659533075874813)
                    ·
                      refine ⟨2555106951247324903453055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6813618536659533075874813 2555106951247324903453055)
                      ·
                        rfl

theorem cell23_4976053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_4976053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4976053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4976053 prefixEnd_4976053 := by exact prefixLift 4976053
  have htrace : WordTrace (prefixWord ++ tailWord_4976053) baseStart_4976053 baseEnd_4976053 := by
    simpa [prefixWord, tailWord_4976053, baseEnd_4976053] using wordTrace_append hprefix tailTrace_4976053
  have hstable : (prefixWord ++ tailWord_4976053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4976053).length < 2 ^ (prefixWord ++ tailWord_4976053).sum := by decide
  have hdescent : baseEnd_4976053 < baseStart_4976053 := by decide
  rcases family_descends (prefixWord ++ tailWord_4976053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4976060 : List Nat := [2, 2, 2, 4, 2, 2, 1, 2, 2, 4]
def baseStart_4976060 : Nat := 118140960795 + 4976060 * 2 ^ 59
def prefixEnd_4976060 : Nat := 4983230072969 + 3 ^ 40 * 4976060 * 2
def baseEnd_4976060 : Nat := 851703515203968792021841

theorem tailTrace_4976060 : CollatzResearch.WordTrace tailWord_4976060 prefixEnd_4976060 851703515203968792021841 := by
  unfold tailWord_4976060
  simp only [CollatzResearch.WordTrace]
  refine ⟨90745909176295969116810817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120994545568394625489081089 90745909176295969116810817)
  ·
    refine ⟨68059431882221976837608113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90745909176295969116810817 68059431882221976837608113)
    ·
      refine ⟨51044573911666482628206085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68059431882221976837608113 51044573911666482628206085)
      ·
        refine ⟨9570857608437465492788641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51044573911666482628206085 9570857608437465492788641)
        ·
          refine ⟨7178143206328099119591481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9570857608437465492788641 7178143206328099119591481)
          ·
            refine ⟨5383607404746074339693611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7178143206328099119591481 5383607404746074339693611)
            ·
              refine ⟨8075411107119111509540417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5383607404746074339693611 8075411107119111509540417)
              ·
                refine ⟨6056558330339333632155313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8075411107119111509540417 6056558330339333632155313)
                ·
                  refine ⟨4542418747754500224116485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6056558330339333632155313 4542418747754500224116485)
                  ·
                    refine ⟨851703515203968792021841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4542418747754500224116485 851703515203968792021841)
                    ·
                      rfl

theorem cell23_4976060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 2, 2, 4].length) (baseStart_4976060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4976060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4976060 prefixEnd_4976060 := by exact prefixLift 4976060
  have htrace : WordTrace (prefixWord ++ tailWord_4976060) baseStart_4976060 baseEnd_4976060 := by
    simpa [prefixWord, tailWord_4976060, baseEnd_4976060] using wordTrace_append hprefix tailTrace_4976060
  have hstable : (prefixWord ++ tailWord_4976060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4976060).length < 2 ^ (prefixWord ++ tailWord_4976060).sum := by decide
  have hdescent : baseEnd_4976060 < baseStart_4976060 := by decide
  rcases family_descends (prefixWord ++ tailWord_4976060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4976119 : List Nat := [1, 1, 3, 1, 1, 1, 1, 6, 2, 2, 4]
def baseStart_4976119 : Nat := 118140960795 + 4976119 * 2 ^ 59
def prefixEnd_4976119 : Nat := 4983230072969 + 3 ^ 40 * 4976119 * 2
def baseEnd_4976119 : Nat := 2555140840970521645227751

theorem tailTrace_4976119 : CollatzResearch.WordTrace tailWord_4976119 prefixEnd_4976119 2555140840970521645227751 := by
  unfold tailWord_4976119
  simp only [CollatzResearch.WordTrace]
  refine ⟨181493970259378191310019411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120995980172918794206679607 181493970259378191310019411)
  ·
    refine ⟨272240955389067286965029117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181493970259378191310019411 272240955389067286965029117)
    ·
      refine ⟨102090358270900232611885919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 272240955389067286965029117 102090358270900232611885919)
      ·
        refine ⟨153135537406350348917828879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102090358270900232611885919 153135537406350348917828879)
        ·
          refine ⟨229703306109525523376743319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153135537406350348917828879 229703306109525523376743319)
          ·
            refine ⟨344554959164288285065114979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229703306109525523376743319 344554959164288285065114979)
            ·
              refine ⟨516832438746432427597672469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 344554959164288285065114979 516832438746432427597672469)
              ·
                refine ⟨24226520566239020043640897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 516832438746432427597672469 24226520566239020043640897)
                ·
                  refine ⟨18169890424679265032730673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24226520566239020043640897 18169890424679265032730673)
                  ·
                    refine ⟨13627417818509448774548005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18169890424679265032730673 13627417818509448774548005)
                    ·
                      refine ⟨2555140840970521645227751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13627417818509448774548005 2555140840970521645227751)
                      ·
                        rfl

theorem cell23_4976119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 2, 2, 4].length) (baseStart_4976119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4976119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4976119 prefixEnd_4976119 := by exact prefixLift 4976119
  have htrace : WordTrace (prefixWord ++ tailWord_4976119) baseStart_4976119 baseEnd_4976119 := by
    simpa [prefixWord, tailWord_4976119, baseEnd_4976119] using wordTrace_append hprefix tailTrace_4976119
  have hstable : (prefixWord ++ tailWord_4976119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4976119).length < 2 ^ (prefixWord ++ tailWord_4976119).sum := by decide
  have hdescent : baseEnd_4976119 < baseStart_4976119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4976119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4976159 : List Nat := [1, 1, 2, 4, 1, 1, 2, 3, 1, 7]
def baseStart_4976159 : Nat := 118140960795 + 4976159 * 2 ^ 59
def prefixEnd_4976159 : Nat := 4983230072969 + 3 ^ 40 * 4976159 * 2
def baseEnd_4976159 : Nat := 851720460065567162909189

theorem tailTrace_4976159 : CollatzResearch.WordTrace tailWord_4976159 prefixEnd_4976159 851720460065567162909189 := by
  unfold tailWord_4976159
  simp only [CollatzResearch.WordTrace]
  refine ⟨181495429179233278141475531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120996952786155518760983687 181495429179233278141475531)
  ·
    refine ⟨272243143768849917212213297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181495429179233278141475531 272243143768849917212213297)
    ·
      refine ⟨204182357826637437909159973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 272243143768849917212213297 204182357826637437909159973)
      ·
        refine ⟨38284192092494519607967495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 204182357826637437909159973 38284192092494519607967495)
        ·
          refine ⟨57426288138741779411951243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38284192092494519607967495 57426288138741779411951243)
          ·
            refine ⟨86139432208112669117926865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57426288138741779411951243 86139432208112669117926865)
            ·
              refine ⟨64604574156084501838445149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86139432208112669117926865 64604574156084501838445149)
              ·
                refine ⟨24226715308531688189416931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64604574156084501838445149 24226715308531688189416931)
                ·
                  refine ⟨36340072962797532284125397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24226715308531688189416931 36340072962797532284125397)
                  ·
                    refine ⟨851720460065567162909189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36340072962797532284125397 851720460065567162909189)
                    ·
                      rfl

theorem cell23_4976159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 7].length) (baseStart_4976159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4976159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4976159 prefixEnd_4976159 := by exact prefixLift 4976159
  have htrace : WordTrace (prefixWord ++ tailWord_4976159) baseStart_4976159 baseEnd_4976159 := by
    simpa [prefixWord, tailWord_4976159, baseEnd_4976159] using wordTrace_append hprefix tailTrace_4976159
  have hstable : (prefixWord ++ tailWord_4976159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4976159).length < 2 ^ (prefixWord ++ tailWord_4976159).sum := by decide
  have hdescent : baseEnd_4976159 < baseStart_4976159 := by decide
  rcases family_descends (prefixWord ++ tailWord_4976159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4976214 : List Nat := [5, 2, 2, 2, 1, 1, 2, 3, 5]
def baseStart_4976214 : Nat := 118140960795 + 4976214 * 2 ^ 59
def prefixEnd_4976214 : Nat := 4983230072969 + 3 ^ 40 * 4976214 * 2
def baseEnd_4976214 : Nat := 283909957959188752615535

theorem tailTrace_4976214 : CollatzResearch.WordTrace tailWord_4976214 prefixEnd_4976214 283909957959188752615535 := by
  unfold tailWord_4976214
  simp only [CollatzResearch.WordTrace]
  refine ⟨11343589699627126408420481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 120998290129356015023151797 11343589699627126408420481)
  ·
    refine ⟨8507692274720344806315361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11343589699627126408420481 8507692274720344806315361)
    ·
      refine ⟨6380769206040258604736521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8507692274720344806315361 6380769206040258604736521)
      ·
        refine ⟨4785576904530193953552391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6380769206040258604736521 4785576904530193953552391)
        ·
          refine ⟨7178365356795290930328587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4785576904530193953552391 7178365356795290930328587)
          ·
            refine ⟨10767548035192936395492881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7178365356795290930328587 10767548035192936395492881)
            ·
              refine ⟨8075661026394702296619661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10767548035192936395492881 8075661026394702296619661)
              ·
                refine ⟨3028372884898013361232373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8075661026394702296619661 3028372884898013361232373)
                ·
                  refine ⟨283909957959188752615535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3028372884898013361232373 283909957959188752615535)
                  ·
                    rfl

theorem cell23_4976214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_4976214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4976214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4976214 prefixEnd_4976214 := by exact prefixLift 4976214
  have htrace : WordTrace (prefixWord ++ tailWord_4976214) baseStart_4976214 baseEnd_4976214 := by
    simpa [prefixWord, tailWord_4976214, baseEnd_4976214] using wordTrace_append hprefix tailTrace_4976214
  have hstable : (prefixWord ++ tailWord_4976214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4976214).length < 2 ^ (prefixWord ++ tailWord_4976214).sum := by decide
  have hdescent : baseEnd_4976214 < baseStart_4976214 := by decide
  rcases family_descends (prefixWord ++ tailWord_4976214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4976240 : List Nat := [2, 1, 1, 1, 6, 1, 2, 4, 1, 4]
def baseStart_4976240 : Nat := 118140960795 + 4976240 * 2 ^ 59
def prefixEnd_4976240 : Nat := 4983230072969 + 3 ^ 40 * 4976240 * 2
def baseEnd_4976240 : Nat := 851734324043238557271565

theorem tailTrace_4976240 : CollatzResearch.WordTrace tailWord_4976240 prefixEnd_4976240 851734324043238557271565 := by
  unfold tailWord_4976240
  simp only [CollatzResearch.WordTrace]
  refine ⟨90749191745969914487587087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120998922327959885983449449 90749191745969914487587087)
  ·
    refine ⟨136123787618954871731380631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90749191745969914487587087 136123787618954871731380631)
    ·
      refine ⟨204185681428432307597070947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136123787618954871731380631 204185681428432307597070947)
      ·
        refine ⟨306278522142648461395606421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204185681428432307597070947 306278522142648461395606421)
        ·
          refine ⟨14356805725436646627919051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 306278522142648461395606421 14356805725436646627919051)
          ·
            refine ⟨21535208588154969941878577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14356805725436646627919051 21535208588154969941878577)
            ·
              refine ⟨16151406441116227456408933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21535208588154969941878577 16151406441116227456408933)
              ·
                refine ⟨3028388707709292648076675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16151406441116227456408933 3028388707709292648076675)
                ·
                  refine ⟨4542583061563938972115013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3028388707709292648076675 4542583061563938972115013)
                  ·
                    refine ⟨851734324043238557271565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4542583061563938972115013 851734324043238557271565)
                    ·
                      rfl

theorem cell23_4976240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 4, 1, 4].length) (baseStart_4976240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4976240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4976240 prefixEnd_4976240 := by exact prefixLift 4976240
  have htrace : WordTrace (prefixWord ++ tailWord_4976240) baseStart_4976240 baseEnd_4976240 := by
    simpa [prefixWord, tailWord_4976240, baseEnd_4976240] using wordTrace_append hprefix tailTrace_4976240
  have hstable : (prefixWord ++ tailWord_4976240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4976240).length < 2 ^ (prefixWord ++ tailWord_4976240).sum := by decide
  have hdescent : baseEnd_4976240 < baseStart_4976240 := by decide
  rcases family_descends (prefixWord ++ tailWord_4976240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4976274 : List Nat := [3, 2, 3, 1, 3, 2, 1, 3, 1, 4]
def baseStart_4976274 : Nat := 118140960795 + 4976274 * 2 ^ 59
def prefixEnd_4976274 : Nat := 4983230072969 + 3 ^ 40 * 4976274 * 2
def baseEnd_4976274 : Nat := 851740143490656179596513

theorem tailTrace_4976274 : CollatzResearch.WordTrace tailWord_4976274 prefixEnd_4976274 851740143490656179596513 := by
  unfold tailWord_4976274
  simp only [CollatzResearch.WordTrace]
  refine ⟨45374905893454163195477969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120999749049211101854607917 45374905893454163195477969)
  ·
    refine ⟨34031179420090622396608477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45374905893454163195477969 34031179420090622396608477)
    ·
      refine ⟨12761692282533983398728179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34031179420090622396608477 12761692282533983398728179)
      ·
        refine ⟨19142538423800975098092269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12761692282533983398728179 19142538423800975098092269)
        ·
          refine ⟨7178451908925365661784601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19142538423800975098092269 7178451908925365661784601)
          ·
            refine ⟨5383838931694024246338451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7178451908925365661784601 5383838931694024246338451)
            ·
              refine ⟨8075758397541036369507677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5383838931694024246338451 8075758397541036369507677)
              ·
                refine ⟨3028409399077888638565379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8075758397541036369507677 3028409399077888638565379)
                ·
                  refine ⟨4542614098616832957848069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3028409399077888638565379 4542614098616832957848069)
                  ·
                    refine ⟨851740143490656179596513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4542614098616832957848069 851740143490656179596513)
                    ·
                      rfl

theorem cell23_4976274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_4976274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4976274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4976274 prefixEnd_4976274 := by exact prefixLift 4976274
  have htrace : WordTrace (prefixWord ++ tailWord_4976274) baseStart_4976274 baseEnd_4976274 := by
    simpa [prefixWord, tailWord_4976274, baseEnd_4976274] using wordTrace_append hprefix tailTrace_4976274
  have hstable : (prefixWord ++ tailWord_4976274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4976274).length < 2 ^ (prefixWord ++ tailWord_4976274).sum := by decide
  have hdescent : baseEnd_4976274 < baseStart_4976274 := by decide
  rcases family_descends (prefixWord ++ tailWord_4976274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4976320 : List Nat := [2, 1, 1, 2, 4, 1, 2, 1, 5, 2, 2]
def baseStart_4976320 : Nat := 118140960795 + 4976320 * 2 ^ 59
def prefixEnd_4976320 : Nat := 4983230072969 + 3 ^ 40 * 4976320 * 2
def baseEnd_4976320 : Nat := 2555244050582075358814327

theorem tailTrace_4976320 : CollatzResearch.WordTrace tailWord_4976320 prefixEnd_4976320 2555244050582075358814327 := by
  unfold tailWord_4976320
  simp only [CollatzResearch.WordTrace]
  refine ⟨90750650665825001319043207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121000867554433335092057609 90750650665825001319043207)
  ·
    refine ⟨136125975998737501978564811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90750650665825001319043207 136125975998737501978564811)
    ·
      refine ⟨204188963998106252967847217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136125975998737501978564811 204188963998106252967847217)
      ·
        refine ⟨153141722998579689725885413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204188963998106252967847217 153141722998579689725885413)
        ·
          refine ⟨28714073062233691823603515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 153141722998579689725885413 28714073062233691823603515)
          ·
            refine ⟨43071109593350537735405273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28714073062233691823603515 43071109593350537735405273)
            ·
              refine ⟨32303332195012903301553955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43071109593350537735405273 32303332195012903301553955)
              ·
                refine ⟨48454998292519354952330933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32303332195012903301553955 48454998292519354952330933)
                ·
                  refine ⟨4542656089923689526781025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48454998292519354952330933 4542656089923689526781025)
                  ·
                    refine ⟨3406992067442767145085769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4542656089923689526781025 3406992067442767145085769)
                    ·
                      refine ⟨2555244050582075358814327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3406992067442767145085769 2555244050582075358814327)
                      ·
                        rfl

theorem cell23_4976320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 5, 2, 2].length) (baseStart_4976320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4976320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4976320 prefixEnd_4976320 := by exact prefixLift 4976320
  have htrace : WordTrace (prefixWord ++ tailWord_4976320) baseStart_4976320 baseEnd_4976320 := by
    simpa [prefixWord, tailWord_4976320, baseEnd_4976320] using wordTrace_append hprefix tailTrace_4976320
  have hstable : (prefixWord ++ tailWord_4976320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4976320).length < 2 ^ (prefixWord ++ tailWord_4976320).sum := by decide
  have hdescent : baseEnd_4976320 < baseStart_4976320 := by decide
  rcases family_descends (prefixWord ++ tailWord_4976320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4976340 : List Nat := [2, 4, 1, 3, 1, 1, 3, 1, 1, 1, 5]
def baseStart_4976340 : Nat := 118140960795 + 4976340 * 2 ^ 59
def prefixEnd_4976340 : Nat := 4983230072969 + 3 ^ 40 * 4976340 * 2
def baseEnd_4976340 : Nat := 2555254320195165280564235

theorem tailTrace_4976340 : CollatzResearch.WordTrace tailWord_4976340 prefixEnd_4976340 2555254320195165280564235 := by
  unfold tailWord_4976340
  simp only [CollatzResearch.WordTrace]
  refine ⟨90751015395788773026907237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121001353861051697369209649 90751015395788773026907237)
  ·
    refine ⟨17015815386710394942545107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90751015395788773026907237 17015815386710394942545107)
    ·
      refine ⟨25523723080065592413817661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17015815386710394942545107 25523723080065592413817661)
      ·
        refine ⟨9571396155024597155181623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25523723080065592413817661 9571396155024597155181623)
        ·
          refine ⟨14357094232536895732772435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9571396155024597155181623 14357094232536895732772435)
          ·
            refine ⟨21535641348805343599158653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14357094232536895732772435 21535641348805343599158653)
            ·
              refine ⟨8075865505802003849684495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21535641348805343599158653 8075865505802003849684495)
              ·
                refine ⟨12113798258703005774526743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8075865505802003849684495 12113798258703005774526743)
                ·
                  refine ⟨18170697388054508661790115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12113798258703005774526743 18170697388054508661790115)
                  ·
                    refine ⟨27256046082081762992685173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18170697388054508661790115 27256046082081762992685173)
                    ·
                      refine ⟨2555254320195165280564235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27256046082081762992685173 2555254320195165280564235)
                      ·
                        rfl

theorem cell23_4976340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_4976340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4976340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4976340 prefixEnd_4976340 := by exact prefixLift 4976340
  have htrace : WordTrace (prefixWord ++ tailWord_4976340) baseStart_4976340 baseEnd_4976340 := by
    simpa [prefixWord, tailWord_4976340, baseEnd_4976340] using wordTrace_append hprefix tailTrace_4976340
  have hstable : (prefixWord ++ tailWord_4976340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4976340).length < 2 ^ (prefixWord ++ tailWord_4976340).sum := by decide
  have hdescent : baseEnd_4976340 < baseStart_4976340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4976340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4976348 : List Nat := [2, 2, 5, 1, 2, 2, 2, 2, 1, 1, 3]
def baseStart_4976348 : Nat := 118140960795 + 4976348 * 2 ^ 59
def prefixEnd_4976348 : Nat := 4983230072969 + 3 ^ 40 * 4976348 * 2
def baseEnd_4976348 : Nat := 2555258428040401249264199

theorem tailTrace_4976348 : CollatzResearch.WordTrace tailWord_4976348 prefixEnd_4976348 2555258428040401249264199 := by
  unfold tailWord_4976348
  simp only [CollatzResearch.WordTrace]
  refine ⟨90751161287774281710052849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121001548383699042280070465 90751161287774281710052849)
  ·
    refine ⟨68063370965830711282539637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90751161287774281710052849 68063370965830711282539637)
    ·
      refine ⟨6380941028046629182738091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 68063370965830711282539637 6380941028046629182738091)
      ·
        refine ⟨9571411542069943774107137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6380941028046629182738091 9571411542069943774107137)
        ·
          refine ⟨7178558656552457830580353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9571411542069943774107137 7178558656552457830580353)
          ·
            refine ⟨5383918992414343372935265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7178558656552457830580353 5383918992414343372935265)
            ·
              refine ⟨4037939244310757529701449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5383918992414343372935265 4037939244310757529701449)
              ·
                refine ⟨3028454433233068147276087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4037939244310757529701449 3028454433233068147276087)
                ·
                  refine ⟨4542681649849602220914131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3028454433233068147276087 4542681649849602220914131)
                  ·
                    refine ⟨6814022474774403331371197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4542681649849602220914131 6814022474774403331371197)
                    ·
                      refine ⟨2555258428040401249264199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6814022474774403331371197 2555258428040401249264199)
                      ·
                        rfl

theorem cell23_4976348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_4976348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4976348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4976348 prefixEnd_4976348 := by exact prefixLift 4976348
  have htrace : WordTrace (prefixWord ++ tailWord_4976348) baseStart_4976348 baseEnd_4976348 := by
    simpa [prefixWord, tailWord_4976348, baseEnd_4976348] using wordTrace_append hprefix tailTrace_4976348
  have hstable : (prefixWord ++ tailWord_4976348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4976348).length < 2 ^ (prefixWord ++ tailWord_4976348).sum := by decide
  have hdescent : baseEnd_4976348 < baseStart_4976348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4976348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4976356 : List Nat := [2, 3, 1, 1, 1, 3, 1, 1, 1, 9]
def baseStart_4976356 : Nat := 118140960795 + 4976356 * 2 ^ 59
def prefixEnd_4976356 : Nat := 4983230072969 + 3 ^ 40 * 4976356 * 2
def baseEnd_4976356 : Nat := 851754178628545739321387

theorem tailTrace_4976356 : CollatzResearch.WordTrace tailWord_4976356 prefixEnd_4976356 851754178628545739321387 := by
  unfold tailWord_4976356
  simp only [CollatzResearch.WordTrace]
  refine ⟨90751307179759790393198461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121001742906346387190931281 90751307179759790393198461)
  ·
    refine ⟨34031740192409921397449423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90751307179759790393198461 34031740192409921397449423)
    ·
      refine ⟨51047610288614882096174135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34031740192409921397449423 51047610288614882096174135)
      ·
        refine ⟨76571415432922323144261203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51047610288614882096174135 76571415432922323144261203)
        ·
          refine ⟨114857123149383484716391805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76571415432922323144261203 114857123149383484716391805)
          ·
            refine ⟨43071421181018806768646927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114857123149383484716391805 43071421181018806768646927)
            ·
              refine ⟨64607131771528210152970391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43071421181018806768646927 64607131771528210152970391)
              ·
                refine ⟨96910697657292315229455587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64607131771528210152970391 96910697657292315229455587)
                ·
                  refine ⟨145366046485938472844183381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96910697657292315229455587 145366046485938472844183381)
                  ·
                    refine ⟨851754178628545739321387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 145366046485938472844183381 851754178628545739321387)
                    ·
                      rfl

theorem cell23_4976356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 1, 9].length) (baseStart_4976356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4976356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4976356 prefixEnd_4976356 := by exact prefixLift 4976356
  have htrace : WordTrace (prefixWord ++ tailWord_4976356) baseStart_4976356 baseEnd_4976356 := by
    simpa [prefixWord, tailWord_4976356, baseEnd_4976356] using wordTrace_append hprefix tailTrace_4976356
  have hstable : (prefixWord ++ tailWord_4976356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4976356).length < 2 ^ (prefixWord ++ tailWord_4976356).sum := by decide
  have hdescent : baseEnd_4976356 < baseStart_4976356 := by decide
  rcases family_descends (prefixWord ++ tailWord_4976356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4976370 : List Nat := [3, 2, 1, 3, 1, 1, 4, 1, 1, 3, 3]
def baseStart_4976370 : Nat := 118140960795 + 4976370 * 2 ^ 59
def prefixEnd_4976370 : Nat := 4983230072969 + 3 ^ 40 * 4976370 * 2
def baseEnd_4976370 : Nat := 2555269724614800163189097

theorem tailTrace_4976370 : CollatzResearch.WordTrace tailWord_4976370 prefixEnd_4976370 2555269724614800163189097 := by
  unfold tailWord_4976370
  simp only [CollatzResearch.WordTrace]
  refine ⟨45375781245367215294351641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121002083320979240784937709 45375781245367215294351641)
  ·
    refine ⟨34031835934025411470763731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45375781245367215294351641 34031835934025411470763731)
    ·
      refine ⟨51047753901038117206145597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34031835934025411470763731 51047753901038117206145597)
      ·
        refine ⟨19142907712889293952304599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51047753901038117206145597 19142907712889293952304599)
        ·
          refine ⟨28714361569333940928456899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19142907712889293952304599 28714361569333940928456899)
          ·
            refine ⟨43071542354000911392685349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28714361569333940928456899 43071542354000911392685349)
            ·
              refine ⟨8075914191375170886128503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43071542354000911392685349 8075914191375170886128503)
              ·
                refine ⟨12113871287062756329192755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8075914191375170886128503 12113871287062756329192755)
                ·
                  refine ⟨18170806930594134493789133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12113871287062756329192755 18170806930594134493789133)
                  ·
                    refine ⟨6814052598972800435170925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18170806930594134493789133 6814052598972800435170925)
                    ·
                      refine ⟨2555269724614800163189097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6814052598972800435170925 2555269724614800163189097)
                      ·
                        rfl

theorem cell23_4976370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_4976370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4976370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4976370 prefixEnd_4976370 := by exact prefixLift 4976370
  have htrace : WordTrace (prefixWord ++ tailWord_4976370) baseStart_4976370 baseEnd_4976370 := by
    simpa [prefixWord, tailWord_4976370, baseEnd_4976370] using wordTrace_append hprefix tailTrace_4976370
  have hstable : (prefixWord ++ tailWord_4976370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4976370).length < 2 ^ (prefixWord ++ tailWord_4976370).sum := by decide
  have hdescent : baseEnd_4976370 < baseStart_4976370 := by decide
  rcases family_descends (prefixWord ++ tailWord_4976370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4976380 : List Nat := [2, 2, 2, 1, 3, 1, 1, 3, 3, 3, 2]
def baseStart_4976380 : Nat := 118140960795 + 4976380 * 2 ^ 59
def prefixEnd_4976380 : Nat := 4983230072969 + 3 ^ 40 * 4976380 * 2
def baseEnd_4976380 : Nat := 2555274859421345124064051

theorem tailTrace_4976380 : CollatzResearch.WordTrace tailWord_4976380 prefixEnd_4976380 2555274859421345124064051 := by
  unfold tailWord_4976380
  simp only [CollatzResearch.WordTrace]
  refine ⟨90751744855716316442635297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121002326474288421923513729 90751744855716316442635297)
  ·
    refine ⟨68063808641787237331976473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90751744855716316442635297 68063808641787237331976473)
    ·
      refine ⟨51047856481340427998982355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68063808641787237331976473 51047856481340427998982355)
      ·
        refine ⟨76571784722010641998473533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51047856481340427998982355 76571784722010641998473533)
        ·
          refine ⟨28714419270753990749427575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76571784722010641998473533 28714419270753990749427575)
          ·
            refine ⟨43071628906130986124141363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28714419270753990749427575 43071628906130986124141363)
            ·
              refine ⟨64607443359196479186212045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43071628906130986124141363 64607443359196479186212045)
              ·
                refine ⟨24227791259698679694829517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64607443359196479186212045 24227791259698679694829517)
                ·
                  refine ⟨9085421722387004885561069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24227791259698679694829517 9085421722387004885561069)
                  ·
                    refine ⟨3407033145895126832085401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9085421722387004885561069 3407033145895126832085401)
                    ·
                      refine ⟨2555274859421345124064051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3407033145895126832085401 2555274859421345124064051)
                      ·
                        rfl

theorem cell23_4976380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 3, 3, 2].length) (baseStart_4976380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4976380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4976380 prefixEnd_4976380 := by exact prefixLift 4976380
  have htrace : WordTrace (prefixWord ++ tailWord_4976380) baseStart_4976380 baseEnd_4976380 := by
    simpa [prefixWord, tailWord_4976380, baseEnd_4976380] using wordTrace_append hprefix tailTrace_4976380
  have hstable : (prefixWord ++ tailWord_4976380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4976380).length < 2 ^ (prefixWord ++ tailWord_4976380).sum := by decide
  have hdescent : baseEnd_4976380 < baseStart_4976380 := by decide
  rcases family_descends (prefixWord ++ tailWord_4976380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4976391 : List Nat := [1, 1, 4, 4, 3, 1, 2, 1, 1, 2, 3]
def baseStart_4976391 : Nat := 118140960795 + 4976391 * 2 ^ 59
def prefixEnd_4976391 : Nat := 4983230072969 + 3 ^ 40 * 4976391 * 2
def baseEnd_4976391 : Nat := 2555280507708544581026501

theorem tailTrace_4976391 : CollatzResearch.WordTrace tailWord_4976391 prefixEnd_4976391 2555280507708544581026501 := by
  unfold tailWord_4976391
  simp only [CollatzResearch.WordTrace]
  refine ⟨181503890914392781763921027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121002593942928521175947351 181503890914392781763921027)
  ·
    refine ⟨272255836371589172645881541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181503890914392781763921027 272255836371589172645881541)
    ·
      refine ⟨51047969319672969871102789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 272255836371589172645881541 51047969319672969871102789)
      ·
        refine ⟨9571494247438681850831773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51047969319672969871102789 9571494247438681850831773)
        ·
          refine ⟨3589310342789505694061915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9571494247438681850831773 3589310342789505694061915)
          ·
            refine ⟨5383965514184258541092873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3589310342789505694061915 5383965514184258541092873)
            ·
              refine ⟨4037974135638193905819655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5383965514184258541092873 4037974135638193905819655)
              ·
                refine ⟨6056961203457290858729483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4037974135638193905819655 6056961203457290858729483)
                ·
                  refine ⟨9085441805185936288094225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6056961203457290858729483 9085441805185936288094225)
                  ·
                    refine ⟨6814081353889452216070669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9085441805185936288094225 6814081353889452216070669)
                    ·
                      refine ⟨2555280507708544581026501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6814081353889452216070669 2555280507708544581026501)
                      ·
                        rfl

theorem cell23_4976391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_4976391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4976391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4976391 prefixEnd_4976391 := by exact prefixLift 4976391
  have htrace : WordTrace (prefixWord ++ tailWord_4976391) baseStart_4976391 baseEnd_4976391 := by
    simpa [prefixWord, tailWord_4976391, baseEnd_4976391] using wordTrace_append hprefix tailTrace_4976391
  have hstable : (prefixWord ++ tailWord_4976391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4976391).length < 2 ^ (prefixWord ++ tailWord_4976391).sum := by decide
  have hdescent : baseEnd_4976391 < baseStart_4976391 := by decide
  rcases family_descends (prefixWord ++ tailWord_4976391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4976433 : List Nat := [1, 2, 2, 3, 2, 2, 2, 2, 7]
def baseStart_4976433 : Nat := 118140960795 + 4976433 * 2 ^ 59
def prefixEnd_4976433 : Nat := 4983230072969 + 3 ^ 40 * 4976433 * 2
def baseEnd_4976433 : Nat := 283922452655114824077923

theorem tailTrace_4976433 : CollatzResearch.WordTrace tailWord_4976433 prefixEnd_4976433 283922452655114824077923 := by
  unfold tailWord_4976433
  simp only [CollatzResearch.WordTrace]
  refine ⟨181505422780240622936949953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121003615186827081957966635 181505422780240622936949953)
  ·
    refine ⟨136129067085180467202712465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181505422780240622936949953 136129067085180467202712465)
    ·
      refine ⟨102096800313885350402034349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136129067085180467202712465 102096800313885350402034349)
      ·
        refine ⟨38286300117707006400762881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102096800313885350402034349 38286300117707006400762881)
        ·
          refine ⟨28714725088280254800572161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38286300117707006400762881 28714725088280254800572161)
          ·
            refine ⟨21536043816210191100429121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28714725088280254800572161 21536043816210191100429121)
            ·
              refine ⟨16152032862157643325321841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21536043816210191100429121 16152032862157643325321841)
              ·
                refine ⟨12114024646618232493991381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16152032862157643325321841 12114024646618232493991381)
                ·
                  refine ⟨283922452655114824077923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12114024646618232493991381 283922452655114824077923)
                  ·
                    rfl

theorem cell23_4976433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 2, 7].length) (baseStart_4976433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4976433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4976433 prefixEnd_4976433 := by exact prefixLift 4976433
  have htrace : WordTrace (prefixWord ++ tailWord_4976433) baseStart_4976433 baseEnd_4976433 := by
    simpa [prefixWord, tailWord_4976433, baseEnd_4976433] using wordTrace_append hprefix tailTrace_4976433
  have hstable : (prefixWord ++ tailWord_4976433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4976433).length < 2 ^ (prefixWord ++ tailWord_4976433).sum := by decide
  have hdescent : baseEnd_4976433 < baseStart_4976433 := by decide
  rcases family_descends (prefixWord ++ tailWord_4976433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4976473 : List Nat := [1, 2, 1, 2, 2, 3, 3, 1, 1, 2, 5]
def baseStart_4976473 : Nat := 118140960795 + 4976473 * 2 ^ 59
def prefixEnd_4976473 : Nat := 4983230072969 + 3 ^ 40 * 4976473 * 2
def baseEnd_4976473 : Nat := 2555322613122213260201123

theorem tailTrace_4976473 : CollatzResearch.WordTrace tailWord_4976473 prefixEnd_4976473 2555322613122213260201123 := by
  unfold tailWord_4976473
  simp only [CollatzResearch.WordTrace]
  refine ⟨181506881700095709768406073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121004587800063806512270715 181506881700095709768406073)
  ·
    refine ⟨136130161275071782326304555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181506881700095709768406073 136130161275071782326304555)
    ·
      refine ⟨204195241912607673489456833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136130161275071782326304555 204195241912607673489456833)
      ·
        refine ⟨153146431434455755117092625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204195241912607673489456833 153146431434455755117092625)
        ·
          refine ⟨114859823575841816337819469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153146431434455755117092625 114859823575841816337819469)
          ·
            refine ⟨43072433840940681126682301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114859823575841816337819469 43072433840940681126682301)
            ·
              refine ⟨16152162690352755422505863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43072433840940681126682301 16152162690352755422505863)
              ·
                refine ⟨24228244035529133133758795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16152162690352755422505863 24228244035529133133758795)
                ·
                  refine ⟨36342366053293699700638193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24228244035529133133758795 36342366053293699700638193)
                  ·
                    refine ⟨27256774539970274775478645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36342366053293699700638193 27256774539970274775478645)
                    ·
                      refine ⟨2555322613122213260201123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27256774539970274775478645 2555322613122213260201123)
                      ·
                        rfl

theorem cell23_4976473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 2, 5].length) (baseStart_4976473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4976473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4976473 prefixEnd_4976473 := by exact prefixLift 4976473
  have htrace : WordTrace (prefixWord ++ tailWord_4976473) baseStart_4976473 baseEnd_4976473 := by
    simpa [prefixWord, tailWord_4976473, baseEnd_4976473] using wordTrace_append hprefix tailTrace_4976473
  have hstable : (prefixWord ++ tailWord_4976473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4976473).length < 2 ^ (prefixWord ++ tailWord_4976473).sum := by decide
  have hdescent : baseEnd_4976473 < baseStart_4976473 := by decide
  rcases family_descends (prefixWord ++ tailWord_4976473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4976493 : List Nat := [1, 5, 1, 1, 1, 1, 2, 1, 2, 8]
def baseStart_4976493 : Nat := 118140960795 + 4976493 * 2 ^ 59
def prefixEnd_4976493 : Nat := 4983230072969 + 3 ^ 40 * 4976493 * 2
def baseEnd_4976493 : Nat := 851777627578434393983677

theorem tailTrace_4976493 : CollatzResearch.WordTrace tailWord_4976493 prefixEnd_4976493 851777627578434393983677 := by
  unfold tailWord_4976493
  simp only [CollatzResearch.WordTrace]
  refine ⟨181507611160023253184134133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121005074106682168789422755 181507611160023253184134133)
  ·
    refine ⟨17016338546252179986012575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 181507611160023253184134133 17016338546252179986012575)
    ·
      refine ⟨25524507819378269979018863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17016338546252179986012575 25524507819378269979018863)
      ·
        refine ⟨38286761729067404968528295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25524507819378269979018863 38286761729067404968528295)
        ·
          refine ⟨57430142593601107452792443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38286761729067404968528295 57430142593601107452792443)
          ·
            refine ⟨86145213890401661179188665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57430142593601107452792443 86145213890401661179188665)
            ·
              refine ⟨64608910417801245884391499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86145213890401661179188665 64608910417801245884391499)
              ·
                refine ⟨96913365626701868826587249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64608910417801245884391499 96913365626701868826587249)
                ·
                  refine ⟨72685024220026401619940437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 96913365626701868826587249 72685024220026401619940437)
                  ·
                    refine ⟨851777627578434393983677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 72685024220026401619940437 851777627578434393983677)
                    ·
                      rfl

theorem cell23_4976493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_4976493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4976493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4976493 prefixEnd_4976493 := by exact prefixLift 4976493
  have htrace : WordTrace (prefixWord ++ tailWord_4976493) baseStart_4976493 baseEnd_4976493 := by
    simpa [prefixWord, tailWord_4976493, baseEnd_4976493] using wordTrace_append hprefix tailTrace_4976493
  have hstable : (prefixWord ++ tailWord_4976493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4976493).length < 2 ^ (prefixWord ++ tailWord_4976493).sum := by decide
  have hdescent : baseEnd_4976493 < baseStart_4976493 := by decide
  rcases family_descends (prefixWord ++ tailWord_4976493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4976584 : List Nat := [2, 1, 3, 1, 4, 2, 2, 1, 3, 1, 3]
def baseStart_4976584 : Nat := 118140960795 + 4976584 * 2 ^ 59
def prefixEnd_4976584 : Nat := 4983230072969 + 3 ^ 40 * 4976584 * 2
def baseEnd_4976584 : Nat := 2555379609474862325913113

theorem tailTrace_4976584 : CollatzResearch.WordTrace tailWord_4976584 prefixEnd_4976584 2555379609474862325913113 := by
  unfold tailWord_4976584
  simp only [CollatzResearch.WordTrace]
  refine ⟨90755465101346787862848403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121007286801795717150464537 90755465101346787862848403)
  ·
    refine ⟨136133197652020181794272605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90755465101346787862848403 136133197652020181794272605)
    ·
      refine ⟨51049949119507568172852227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136133197652020181794272605 51049949119507568172852227)
      ·
        refine ⟨76574923679261352259278341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51049949119507568172852227 76574923679261352259278341)
        ·
          refine ⟨14357798189861503548614689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76574923679261352259278341 14357798189861503548614689)
          ·
            refine ⟨10768348642396127661461017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14357798189861503548614689 10768348642396127661461017)
            ·
              refine ⟨8076261481797095746095763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10768348642396127661461017 8076261481797095746095763)
              ·
                refine ⟨12114392222695643619143645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8076261481797095746095763 12114392222695643619143645)
                ·
                  refine ⟨4542897083510866357178867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12114392222695643619143645 4542897083510866357178867)
                  ·
                    refine ⟨6814345625266299535768301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4542897083510866357178867 6814345625266299535768301)
                    ·
                      refine ⟨2555379609474862325913113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6814345625266299535768301 2555379609474862325913113)
                      ·
                        rfl

theorem cell23_4976584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 1, 3, 1, 3].length) (baseStart_4976584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4976584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4976584 prefixEnd_4976584 := by exact prefixLift 4976584
  have htrace : WordTrace (prefixWord ++ tailWord_4976584) baseStart_4976584 baseEnd_4976584 := by
    simpa [prefixWord, tailWord_4976584, baseEnd_4976584] using wordTrace_append hprefix tailTrace_4976584
  have hstable : (prefixWord ++ tailWord_4976584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4976584).length < 2 ^ (prefixWord ++ tailWord_4976584).sum := by decide
  have hdescent : baseEnd_4976584 < baseStart_4976584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4976584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4976607 : List Nat := [1, 1, 2, 3, 4, 1, 1, 4, 1, 1, 4]
def baseStart_4976607 : Nat := 118140960795 + 4976607 * 2 ^ 59
def prefixEnd_4976607 : Nat := 4983230072969 + 3 ^ 40 * 4976607 * 2
def baseEnd_4976607 : Nat := 2555391419529915735925507

theorem tailTrace_4976607 : CollatzResearch.WordTrace tailWord_4976607 prefixEnd_4976607 2555391419529915735925507 := by
  unfold tailWord_4976607
  simp only [CollatzResearch.WordTrace]
  refine ⟨181511769081610250653784075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121007846054406833769189383 181511769081610250653784075)
  ·
    refine ⟨272267653622415375980676113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181511769081610250653784075 272267653622415375980676113)
    ·
      refine ⟨204200740216811531985507085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 272267653622415375980676113 204200740216811531985507085)
      ·
        refine ⟨76575277581304324494565157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 204200740216811531985507085 76575277581304324494565157)
        ·
          refine ⟨14357864546494560842730967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76575277581304324494565157 14357864546494560842730967)
          ·
            refine ⟨21536796819741841264096451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14357864546494560842730967 21536796819741841264096451)
            ·
              refine ⟨32305195229612761896144677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21536796819741841264096451 32305195229612761896144677)
              ·
                refine ⟨6057224105552392855527127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32305195229612761896144677 6057224105552392855527127)
                ·
                  refine ⟨9085836158328589283290691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6057224105552392855527127 9085836158328589283290691)
                  ·
                    refine ⟨13628754237492883924936037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9085836158328589283290691 13628754237492883924936037)
                    ·
                      refine ⟨2555391419529915735925507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13628754237492883924936037 2555391419529915735925507)
                      ·
                        rfl

theorem cell23_4976607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 4, 1, 1, 4].length) (baseStart_4976607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4976607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4976607 prefixEnd_4976607 := by exact prefixLift 4976607
  have htrace : WordTrace (prefixWord ++ tailWord_4976607) baseStart_4976607 baseEnd_4976607 := by
    simpa [prefixWord, tailWord_4976607, baseEnd_4976607] using wordTrace_append hprefix tailTrace_4976607
  have hstable : (prefixWord ++ tailWord_4976607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4976607).length < 2 ^ (prefixWord ++ tailWord_4976607).sum := by decide
  have hdescent : baseEnd_4976607 < baseStart_4976607 := by decide
  rcases family_descends (prefixWord ++ tailWord_4976607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4976620 : List Nat := [2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 4]
def baseStart_4976620 : Nat := 118140960795 + 4976620 * 2 ^ 59
def prefixEnd_4976620 : Nat := 4983230072969 + 3 ^ 40 * 4976620 * 2
def baseEnd_4976620 : Nat := 2555398094778424185062947

theorem tailTrace_4976620 : CollatzResearch.WordTrace tailWord_4976620 prefixEnd_4976620 2555398094778424185062947 := by
  unfold tailWord_4976620
  simp only [CollatzResearch.WordTrace]
  refine ⟨90756121615281576937003657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121008162153708769249338209 90756121615281576937003657)
  ·
    refine ⟨68067091211461182702752743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90756121615281576937003657 68067091211461182702752743)
    ·
      refine ⟨102100636817191774054129115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68067091211461182702752743 102100636817191774054129115)
      ·
        refine ⟨153150955225787661081193673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102100636817191774054129115 153150955225787661081193673)
        ·
          refine ⟨114863216419340745810895255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153150955225787661081193673 114863216419340745810895255)
          ·
            refine ⟨172294824629011118716342883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114863216419340745810895255 172294824629011118716342883)
            ·
              refine ⟨258442236943516678074514325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172294824629011118716342883 258442236943516678074514325)
              ·
                refine ⟨12114479856727344284742859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 258442236943516678074514325 12114479856727344284742859)
                ·
                  refine ⟨18171719785091016427114289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12114479856727344284742859 18171719785091016427114289)
                  ·
                    refine ⟨13628789838818262320335717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18171719785091016427114289 13628789838818262320335717)
                    ·
                      refine ⟨2555398094778424185062947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13628789838818262320335717 2555398094778424185062947)
                      ·
                        rfl

theorem cell23_4976620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 4].length) (baseStart_4976620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4976620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4976620 prefixEnd_4976620 := by exact prefixLift 4976620
  have htrace : WordTrace (prefixWord ++ tailWord_4976620) baseStart_4976620 baseEnd_4976620 := by
    simpa [prefixWord, tailWord_4976620, baseEnd_4976620] using wordTrace_append hprefix tailTrace_4976620
  have hstable : (prefixWord ++ tailWord_4976620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4976620).length < 2 ^ (prefixWord ++ tailWord_4976620).sum := by decide
  have hdescent : baseEnd_4976620 < baseStart_4976620 := by decide
  rcases family_descends (prefixWord ++ tailWord_4976620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4976640 : List Nat := [2, 1, 1, 2, 1, 1, 1, 3, 5, 3, 3]
def baseStart_4976640 : Nat := 118140960795 + 4976640 * 2 ^ 59
def prefixEnd_4976640 : Nat := 4983230072969 + 3 ^ 40 * 4976640 * 2
def baseEnd_4976640 : Nat := 2555408364391514106812855

theorem tailTrace_4976640 : CollatzResearch.WordTrace tailWord_4976640 prefixEnd_4976640 2555408364391514106812855 := by
  unfold tailWord_4976640
  simp only [CollatzResearch.WordTrace]
  refine ⟨90756486345245348644867687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121008648460327131526490249 90756486345245348644867687)
  ·
    refine ⟨136134729517868022967301531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90756486345245348644867687 136134729517868022967301531)
    ·
      refine ⟨204202094276802034450952297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136134729517868022967301531 204202094276802034450952297)
      ·
        refine ⟨153151570707601525838214223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204202094276802034450952297 153151570707601525838214223)
        ·
          refine ⟨229727356061402288757321335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153151570707601525838214223 229727356061402288757321335)
          ·
            refine ⟨344591034092103433135982003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229727356061402288757321335 344591034092103433135982003)
            ·
              refine ⟨516886551138155149703973005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 344591034092103433135982003 516886551138155149703973005)
              ·
                refine ⟨193832456676808181138989877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 516886551138155149703973005 193832456676808181138989877)
                ·
                  refine ⟨18171792813450766981780301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 193832456676808181138989877 18171792813450766981780301)
                  ·
                    refine ⟨6814422305044037618167613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18171792813450766981780301 6814422305044037618167613)
                    ·
                      refine ⟨2555408364391514106812855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6814422305044037618167613 2555408364391514106812855)
                      ·
                        rfl

theorem cell23_4976640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 5, 3, 3].length) (baseStart_4976640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4976640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4976640 prefixEnd_4976640 := by exact prefixLift 4976640
  have htrace : WordTrace (prefixWord ++ tailWord_4976640) baseStart_4976640 baseEnd_4976640 := by
    simpa [prefixWord, tailWord_4976640, baseEnd_4976640] using wordTrace_append hprefix tailTrace_4976640
  have hstable : (prefixWord ++ tailWord_4976640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4976640).length < 2 ^ (prefixWord ++ tailWord_4976640).sum := by decide
  have hdescent : baseEnd_4976640 < baseStart_4976640 := by decide
  rcases family_descends (prefixWord ++ tailWord_4976640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4976661 : List Nat := [1, 3, 2, 1, 5, 2, 1, 2, 1, 2, 3]
def baseStart_4976661 : Nat := 118140960795 + 4976661 * 2 ^ 59
def prefixEnd_4976661 : Nat := 4983230072969 + 3 ^ 40 * 4976661 * 2
def baseEnd_4976661 : Nat := 2555419147485258524650259

theorem tailTrace_4976661 : CollatzResearch.WordTrace tailWord_4976661 prefixEnd_4976661 2555419147485258524650259 := by
  unfold tailWord_4976661
  simp only [CollatzResearch.WordTrace]
  refine ⟨181513738623414617876249837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121009159082276411917499891 181513738623414617876249837)
  ·
    refine ⟨68067651983780481703593689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181513738623414617876249837 68067651983780481703593689)
    ·
      refine ⟨51050738987835361277695267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68067651983780481703593689 51050738987835361277695267)
      ·
        refine ⟨76576108481753041916542901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51050738987835361277695267 76576108481753041916542901)
        ·
          refine ⟨7179010170164347679675897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 76576108481753041916542901 7179010170164347679675897)
          ·
            refine ⟨5384257627623260759756923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7179010170164347679675897 5384257627623260759756923)
            ·
              refine ⟨8076386441434891139635385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5384257627623260759756923 8076386441434891139635385)
              ·
                refine ⟨6057289831076168354726539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8076386441434891139635385 6057289831076168354726539)
                ·
                  refine ⟨9085934746614252532089809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6057289831076168354726539 9085934746614252532089809)
                  ·
                    refine ⟨6814451059960689399067357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9085934746614252532089809 6814451059960689399067357)
                    ·
                      refine ⟨2555419147485258524650259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6814451059960689399067357 2555419147485258524650259)
                      ·
                        rfl

theorem cell23_4976661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 2, 1, 2, 3].length) (baseStart_4976661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4976661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4976661 prefixEnd_4976661 := by exact prefixLift 4976661
  have htrace : WordTrace (prefixWord ++ tailWord_4976661) baseStart_4976661 baseEnd_4976661 := by
    simpa [prefixWord, tailWord_4976661, baseEnd_4976661] using wordTrace_append hprefix tailTrace_4976661
  have hstable : (prefixWord ++ tailWord_4976661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4976661).length < 2 ^ (prefixWord ++ tailWord_4976661).sum := by decide
  have hdescent : baseEnd_4976661 < baseStart_4976661 := by decide
  rcases family_descends (prefixWord ++ tailWord_4976661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4976714 : List Nat := [3, 1, 2, 1, 1, 2, 1, 2, 6, 2, 2]
def baseStart_4976714 : Nat := 118140960795 + 4976714 * 2 ^ 59
def prefixEnd_4976714 : Nat := 4983230072969 + 3 ^ 40 * 4976714 * 2
def baseEnd_4976714 : Nat := 2555446361959946817287515

theorem tailTrace_4976714 : CollatzResearch.WordTrace tailWord_4976714 prefixEnd_4976714 2555446361959946817287515 := by
  unfold tailWord_4976714
  simp only [CollatzResearch.WordTrace]
  refine ⟨45378917923055651981982299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121010447794815071951952797 45378917923055651981982299)
  ·
    refine ⟨68068376884583477972973449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45378917923055651981982299 68068376884583477972973449)
    ·
      refine ⟨51051282663437608479730087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68068376884583477972973449 51051282663437608479730087)
      ·
        refine ⟨76576923995156412719595131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51051282663437608479730087 76576923995156412719595131)
        ·
          refine ⟨114865385992734619079392697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76576923995156412719595131 114865385992734619079392697)
          ·
            refine ⟨86149039494550964309544523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114865385992734619079392697 86149039494550964309544523)
            ·
              refine ⟨129223559241826446464316785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86149039494550964309544523 129223559241826446464316785)
              ·
                refine ⟨96917669431369834848237589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129223559241826446464316785 96917669431369834848237589)
                ·
                  refine ⟨4543015754595461008511137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 96917669431369834848237589 4543015754595461008511137)
                  ·
                    refine ⟨3407261815946595756383353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4543015754595461008511137 3407261815946595756383353)
                    ·
                      refine ⟨2555446361959946817287515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3407261815946595756383353 2555446361959946817287515)
                      ·
                        rfl

theorem cell23_4976714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 6, 2, 2].length) (baseStart_4976714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4976714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4976714 prefixEnd_4976714 := by exact prefixLift 4976714
  have htrace : WordTrace (prefixWord ++ tailWord_4976714) baseStart_4976714 baseEnd_4976714 := by
    simpa [prefixWord, tailWord_4976714, baseEnd_4976714] using wordTrace_append hprefix tailTrace_4976714
  have hstable : (prefixWord ++ tailWord_4976714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4976714).length < 2 ^ (prefixWord ++ tailWord_4976714).sum := by decide
  have hdescent : baseEnd_4976714 < baseStart_4976714 := by decide
  rcases family_descends (prefixWord ++ tailWord_4976714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4976748 : List Nat := [2, 2, 1, 1, 3, 5, 1, 2, 2, 2, 2]
def baseStart_4976748 : Nat := 118140960795 + 4976748 * 2 ^ 59
def prefixEnd_4976748 : Nat := 4983230072969 + 3 ^ 40 * 4976748 * 2
def baseEnd_4976748 : Nat := 2555463820302199684262359

theorem tailTrace_4976748 : CollatzResearch.WordTrace tailWord_4976748 prefixEnd_4976748 2555463820302199684262359 := by
  unfold tailWord_4976748
  simp only [CollatzResearch.WordTrace]
  refine ⟨90758455887049715867333449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121011274516066287823111265 90758455887049715867333449)
  ·
    refine ⟨68068841915287286900500087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90758455887049715867333449 68068841915287286900500087)
    ·
      refine ⟨102103262872930930350750131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68068841915287286900500087 102103262872930930350750131)
      ·
        refine ⟨153154894309396395526125197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102103262872930930350750131 153154894309396395526125197)
        ·
          refine ⟨57433085366023648322296949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 153154894309396395526125197 57433085366023648322296949)
          ·
            refine ⟨5384351753064717030215339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57433085366023648322296949 5384351753064717030215339)
            ·
              refine ⟨8076527629597075545323009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5384351753064717030215339 8076527629597075545323009)
              ·
                refine ⟨6057395722197806658992257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8076527629597075545323009 6057395722197806658992257)
                ·
                  refine ⟨4543046791648354994244193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6057395722197806658992257 4543046791648354994244193)
                  ·
                    refine ⟨3407285093736266245683145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4543046791648354994244193 3407285093736266245683145)
                    ·
                      refine ⟨2555463820302199684262359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3407285093736266245683145 2555463820302199684262359)
                      ·
                        rfl

theorem cell23_4976748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 2, 2].length) (baseStart_4976748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4976748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4976748 prefixEnd_4976748 := by exact prefixLift 4976748
  have htrace : WordTrace (prefixWord ++ tailWord_4976748) baseStart_4976748 baseEnd_4976748 := by
    simpa [prefixWord, tailWord_4976748, baseEnd_4976748] using wordTrace_append hprefix tailTrace_4976748
  have hstable : (prefixWord ++ tailWord_4976748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4976748).length < 2 ^ (prefixWord ++ tailWord_4976748).sum := by decide
  have hdescent : baseEnd_4976748 < baseStart_4976748 := by decide
  rcases family_descends (prefixWord ++ tailWord_4976748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4976754 : List Nat := [3, 2, 1, 2, 2, 2, 2, 4, 5]
def baseStart_4976754 : Nat := 118140960795 + 4976754 * 2 ^ 59
def prefixEnd_4976754 : Nat := 4983230072969 + 3 ^ 40 * 4976754 * 2
def baseEnd_4976754 : Nat := 283940766798458517865259

theorem tailTrace_4976754 : CollatzResearch.WordTrace tailWord_4976754 prefixEnd_4976754 283940766798458517865259 := by
  unfold tailWord_4976754
  simp only [CollatzResearch.WordTrace]
  refine ⟨45379282653019423689846329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121011420408051796506256877 45379282653019423689846329)
  ·
    refine ⟨34034461989764567767384747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45379282653019423689846329 34034461989764567767384747)
    ·
      refine ⟨51051692984646851651077121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34034461989764567767384747 51051692984646851651077121)
      ·
        refine ⟨38288769738485138738307841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51051692984646851651077121 38288769738485138738307841)
        ·
          refine ⟨28716577303863854053730881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38288769738485138738307841 28716577303863854053730881)
          ·
            refine ⟨21537432977897890540298161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28716577303863854053730881 21537432977897890540298161)
            ·
              refine ⟨16153074733423417905223621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21537432977897890540298161 16153074733423417905223621)
              ·
                refine ⟨3028701512516890857229429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16153074733423417905223621 3028701512516890857229429)
                ·
                  refine ⟨283940766798458517865259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3028701512516890857229429 283940766798458517865259)
                  ·
                    rfl

theorem cell23_4976754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 4, 5].length) (baseStart_4976754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4976754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4976754 prefixEnd_4976754 := by exact prefixLift 4976754
  have htrace : WordTrace (prefixWord ++ tailWord_4976754) baseStart_4976754 baseEnd_4976754 := by
    simpa [prefixWord, tailWord_4976754, baseEnd_4976754] using wordTrace_append hprefix tailTrace_4976754
  have hstable : (prefixWord ++ tailWord_4976754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4976754).length < 2 ^ (prefixWord ++ tailWord_4976754).sum := by decide
  have hdescent : baseEnd_4976754 < baseStart_4976754 := by decide
  rcases family_descends (prefixWord ++ tailWord_4976754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4976760 : List Nat := [2, 1, 2, 1, 1, 1, 3, 3, 1, 1, 7]
def baseStart_4976760 : Nat := 118140960795 + 4976760 * 2 ^ 59
def prefixEnd_4976760 : Nat := 4983230072969 + 3 ^ 40 * 4976760 * 2
def baseEnd_4976760 : Nat := 2555469982070053637312303

theorem tailTrace_4976760 : CollatzResearch.WordTrace tailWord_4976760 prefixEnd_4976760 2555469982070053637312303 := by
  unfold tailWord_4976760
  simp only [CollatzResearch.WordTrace]
  refine ⟨90758674725027978892051867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121011566300037305189402489 90758674725027978892051867)
  ·
    refine ⟨136138012087541968338077801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90758674725027978892051867 136138012087541968338077801)
    ·
      refine ⟨102103509065656476253558351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136138012087541968338077801 102103509065656476253558351)
      ·
        refine ⟨153155263598484714380337527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102103509065656476253558351 153155263598484714380337527)
        ·
          refine ⟨229732895397727071570506291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153155263598484714380337527 229732895397727071570506291)
          ·
            refine ⟨344599343096590607355759437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229732895397727071570506291 344599343096590607355759437)
            ·
              refine ⟨129224753661221477758409789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 344599343096590607355759437 129224753661221477758409789)
              ·
                refine ⟨48459282622958054159403671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 129224753661221477758409789 48459282622958054159403671)
                ·
                  refine ⟨72688923934437081239105507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48459282622958054159403671 72688923934437081239105507)
                  ·
                    refine ⟨109033385901655621858658261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 72688923934437081239105507 109033385901655621858658261)
                    ·
                      refine ⟨2555469982070053637312303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 109033385901655621858658261 2555469982070053637312303)
                      ·
                        rfl

theorem cell23_4976760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 1, 1, 7].length) (baseStart_4976760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4976760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4976760 prefixEnd_4976760 := by exact prefixLift 4976760
  have htrace : WordTrace (prefixWord ++ tailWord_4976760) baseStart_4976760 baseEnd_4976760 := by
    simpa [prefixWord, tailWord_4976760, baseEnd_4976760] using wordTrace_append hprefix tailTrace_4976760
  have hstable : (prefixWord ++ tailWord_4976760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4976760).length < 2 ^ (prefixWord ++ tailWord_4976760).sum := by decide
  have hdescent : baseEnd_4976760 < baseStart_4976760 := by decide
  rcases family_descends (prefixWord ++ tailWord_4976760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4976787 : List Nat := [1, 1, 1, 2, 1, 2, 3, 5, 2, 1, 4]
def baseStart_4976787 : Nat := 118140960795 + 4976787 * 2 ^ 59
def prefixEnd_4976787 : Nat := 4983230072969 + 3 ^ 40 * 4976787 * 2
def baseEnd_4976787 : Nat := 2555483846047725031674679

theorem tailTrace_4976787 : CollatzResearch.WordTrace tailWord_4976787 prefixEnd_4976787 2555483846047725031674679 := by
  unfold tailWord_4976787
  simp only [CollatzResearch.WordTrace]
  refine ⟨181518334220958141395336615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121012222813972094263557743 181518334220958141395336615)
  ·
    refine ⟨272277501331437212093004923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181518334220958141395336615 272277501331437212093004923)
    ·
      refine ⟨408416251997155818139507385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272277501331437212093004923 408416251997155818139507385)
      ·
        refine ⟨306312188997866863604630539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 408416251997155818139507385 306312188997866863604630539)
        ·
          refine ⟨459468283496800295406945809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 306312188997866863604630539 459468283496800295406945809)
          ·
            refine ⟨344601212622600221555209357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 459468283496800295406945809 344601212622600221555209357)
            ·
              refine ⟨129225454733475083083203509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 344601212622600221555209357 129225454733475083083203509)
              ·
                refine ⟨12114886381263289039050329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 129225454733475083083203509 12114886381263289039050329)
                ·
                  refine ⟨9086164785947466779287747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12114886381263289039050329 9086164785947466779287747)
                  ·
                    refine ⟨13629247178921200168931621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9086164785947466779287747 13629247178921200168931621)
                    ·
                      refine ⟨2555483846047725031674679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13629247178921200168931621 2555483846047725031674679)
                      ·
                        rfl

theorem cell23_4976787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 5, 2, 1, 4].length) (baseStart_4976787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4976787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4976787 prefixEnd_4976787 := by exact prefixLift 4976787
  have htrace : WordTrace (prefixWord ++ tailWord_4976787) baseStart_4976787 baseEnd_4976787 := by
    simpa [prefixWord, tailWord_4976787, baseEnd_4976787] using wordTrace_append hprefix tailTrace_4976787
  have hstable : (prefixWord ++ tailWord_4976787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4976787).length < 2 ^ (prefixWord ++ tailWord_4976787).sum := by decide
  have hdescent : baseEnd_4976787 < baseStart_4976787 := by decide
  rcases family_descends (prefixWord ++ tailWord_4976787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4976827 : List Nat := [1, 1, 1, 1, 1, 2, 7, 3, 6]
def baseStart_4976827 : Nat := 118140960795 + 4976827 * 2 ^ 59
def prefixEnd_4976827 : Nat := 4983230072969 + 3 ^ 40 * 4976827 * 2
def baseEnd_4976827 : Nat := 283944931697100541686055

theorem tailTrace_4976827 : CollatzResearch.WordTrace tailWord_4976827 prefixEnd_4976827 283944931697100541686055 := by
  unfold tailWord_4976827
  simp only [CollatzResearch.WordTrace]
  refine ⟨181519793140813228226792735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121013195427208818817861823 181519793140813228226792735)
  ·
    refine ⟨272279689711219842340189103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181519793140813228226792735 272279689711219842340189103)
    ·
      refine ⟨408419534566829763510283655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272279689711219842340189103 408419534566829763510283655)
      ·
        refine ⟨612629301850244645265425483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 408419534566829763510283655 612629301850244645265425483)
        ·
          refine ⟨918943952775366967898138225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 612629301850244645265425483 918943952775366967898138225)
          ·
            refine ⟨689207964581525225923603669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 918943952775366967898138225 689207964581525225923603669)
            ·
              refine ⟨16153311669879497482584461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 689207964581525225923603669 16153311669879497482584461)
              ·
                refine ⟨6057491876204811555969173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16153311669879497482584461 6057491876204811555969173)
                ·
                  refine ⟨283944931697100541686055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6057491876204811555969173 283944931697100541686055)
                  ·
                    rfl

theorem cell23_4976827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 3, 6].length) (baseStart_4976827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4976827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4976827 prefixEnd_4976827 := by exact prefixLift 4976827
  have htrace : WordTrace (prefixWord ++ tailWord_4976827) baseStart_4976827 baseEnd_4976827 := by
    simpa [prefixWord, tailWord_4976827, baseEnd_4976827] using wordTrace_append hprefix tailTrace_4976827
  have hstable : (prefixWord ++ tailWord_4976827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4976827).length < 2 ^ (prefixWord ++ tailWord_4976827).sum := by decide
  have hdescent : baseEnd_4976827 < baseStart_4976827 := by decide
  rcases family_descends (prefixWord ++ tailWord_4976827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4976837 : List Nat := [1, 3, 1, 1, 1, 1, 4, 1, 2, 5, 3]
def baseStart_4976837 : Nat := 118140960795 + 4976837 * 2 ^ 59
def prefixEnd_4976837 : Nat := 4983230072969 + 3 ^ 40 * 4976837 * 2
def baseEnd_4976837 : Nat := 2555509520080449836049449

theorem tailTrace_4976837 : CollatzResearch.WordTrace tailWord_4976837 prefixEnd_4976837 2555509520080449836049449 := by
  unfold tailWord_4976837
  simp only [CollatzResearch.WordTrace]
  refine ⟨181520157870776999934656765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121013438580517999956437843 181520157870776999934656765)
  ·
    refine ⟨68070059201541374975496287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181520157870776999934656765 68070059201541374975496287)
    ·
      refine ⟨102105088802312062463244431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68070059201541374975496287 102105088802312062463244431)
      ·
        refine ⟨153157633203468093694866647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102105088802312062463244431 153157633203468093694866647)
        ·
          refine ⟨229736449805202140542299971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153157633203468093694866647 229736449805202140542299971)
          ·
            refine ⟨344604674707803210813449957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229736449805202140542299971 344604674707803210813449957)
            ·
              refine ⟨64613376507713102027521867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 344604674707803210813449957 64613376507713102027521867)
              ·
                refine ⟨96920064761569653041282801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64613376507713102027521867 96920064761569653041282801)
                ·
                  refine ⟨72690048571177239780962101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 96920064761569653041282801 72690048571177239780962101)
                  ·
                    refine ⟨6814692053547866229465197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 72690048571177239780962101 6814692053547866229465197)
                    ·
                      refine ⟨2555509520080449836049449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6814692053547866229465197 2555509520080449836049449)
                      ·
                        rfl

theorem cell23_4976837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 5, 3].length) (baseStart_4976837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4976837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4976837 prefixEnd_4976837 := by exact prefixLift 4976837
  have htrace : WordTrace (prefixWord ++ tailWord_4976837) baseStart_4976837 baseEnd_4976837 := by
    simpa [prefixWord, tailWord_4976837, baseEnd_4976837] using wordTrace_append hprefix tailTrace_4976837
  have hstable : (prefixWord ++ tailWord_4976837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4976837).length < 2 ^ (prefixWord ++ tailWord_4976837).sum := by decide
  have hdescent : baseEnd_4976837 < baseStart_4976837 := by decide
  rcases family_descends (prefixWord ++ tailWord_4976837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4976861 : List Nat := [1, 4, 3, 2, 1, 2, 2, 2, 6]
def baseStart_4976861 : Nat := 118140960795 + 4976861 * 2 ^ 59
def prefixEnd_4976861 : Nat := 4983230072969 + 3 ^ 40 * 4976861 * 2
def baseEnd_4976861 : Nat := 283946871512906415794371

theorem tailTrace_4976861 : CollatzResearch.WordTrace tailWord_4976861 prefixEnd_4976861 283946871512906415794371 := by
  unfold tailWord_4976861
  simp only [CollatzResearch.WordTrace]
  refine ⟨181521033222690052033530437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121014022148460034689020291 181521033222690052033530437)
  ·
    refine ⟨34035193729254384756286957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 181521033222690052033530437 34035193729254384756286957)
    ·
      refine ⟨12763197648470394283607609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34035193729254384756286957 12763197648470394283607609)
      ·
        refine ⟨9572398236352795712705707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12763197648470394283607609 9572398236352795712705707)
        ·
          refine ⟨14358597354529193569058561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9572398236352795712705707 14358597354529193569058561)
          ·
            refine ⟨10768948015896895176793921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14358597354529193569058561 10768948015896895176793921)
            ·
              refine ⟨8076711011922671382595441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10768948015896895176793921 8076711011922671382595441)
              ·
                refine ⟨6057533258942003536946581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8076711011922671382595441 6057533258942003536946581)
                ·
                  refine ⟨283946871512906415794371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6057533258942003536946581 283946871512906415794371)
                  ·
                    rfl

theorem cell23_4976861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 2, 6].length) (baseStart_4976861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4976861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4976861 prefixEnd_4976861 := by exact prefixLift 4976861
  have htrace : WordTrace (prefixWord ++ tailWord_4976861) baseStart_4976861 baseEnd_4976861 := by
    simpa [prefixWord, tailWord_4976861, baseEnd_4976861] using wordTrace_append hprefix tailTrace_4976861
  have hstable : (prefixWord ++ tailWord_4976861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4976861).length < 2 ^ (prefixWord ++ tailWord_4976861).sum := by decide
  have hdescent : baseEnd_4976861 < baseStart_4976861 := by decide
  rcases family_descends (prefixWord ++ tailWord_4976861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4976898 : List Nat := [3, 4, 1, 1, 2, 2, 1, 1, 1, 5, 2]
def baseStart_4976898 : Nat := 118140960795 + 4976898 * 2 ^ 59
def prefixEnd_4976898 : Nat := 4983230072969 + 3 ^ 40 * 4976898 * 2
def baseEnd_4976898 : Nat := 2555540842400374097386669

theorem tailTrace_4976898 : CollatzResearch.WordTrace tailWord_4976898 prefixEnd_4976898 2555540842400374097386669 := by
  unfold tailWord_4976898
  simp only [CollatzResearch.WordTrace]
  refine ⟨45380595680889001838156837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121014921815704004901751565 45380595680889001838156837)
  ·
    refine ⟨8508861690166687844654407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45380595680889001838156837 8508861690166687844654407)
    ·
      refine ⟨12763292535250031766981611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8508861690166687844654407 12763292535250031766981611)
      ·
        refine ⟨19144938802875047650472417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12763292535250031766981611 19144938802875047650472417)
        ·
          refine ⟨14358704102156285737854313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19144938802875047650472417 14358704102156285737854313)
          ·
            refine ⟨10769028076617214303390735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14358704102156285737854313 10769028076617214303390735)
            ·
              refine ⟨16153542114925821455086103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10769028076617214303390735 16153542114925821455086103)
              ·
                refine ⟨24230313172388732182629155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16153542114925821455086103 24230313172388732182629155)
                ·
                  refine ⟨36345469758583098273943733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24230313172388732182629155 36345469758583098273943733)
                  ·
                    refine ⟨3407387789867165463182225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36345469758583098273943733 3407387789867165463182225)
                    ·
                      refine ⟨2555540842400374097386669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3407387789867165463182225 2555540842400374097386669)
                      ·
                        rfl

theorem cell23_4976898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 1, 5, 2].length) (baseStart_4976898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4976898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4976898 prefixEnd_4976898 := by exact prefixLift 4976898
  have htrace : WordTrace (prefixWord ++ tailWord_4976898) baseStart_4976898 baseEnd_4976898 := by
    simpa [prefixWord, tailWord_4976898, baseEnd_4976898] using wordTrace_append hprefix tailTrace_4976898
  have hstable : (prefixWord ++ tailWord_4976898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4976898).length < 2 ^ (prefixWord ++ tailWord_4976898).sum := by decide
  have hdescent : baseEnd_4976898 < baseStart_4976898 := by decide
  rcases family_descends (prefixWord ++ tailWord_4976898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4976904 : List Nat := [2, 1, 3, 2, 3, 1, 2, 2, 1, 6]
def baseStart_4976904 : Nat := 118140960795 + 4976904 * 2 ^ 59
def prefixEnd_4976904 : Nat := 4983230072969 + 3 ^ 40 * 4976904 * 2
def baseEnd_4976904 : Nat := 851847974428100357970547

theorem tailTrace_4976904 : CollatzResearch.WordTrace tailWord_4976904 prefixEnd_4976904 851847974428100357970547 := by
  unfold tailWord_4976904
  simp only [CollatzResearch.WordTrace]
  refine ⟨90761300780767135188672883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121015067707689513584897177 90761300780767135188672883)
  ·
    refine ⟨136141951171150702783009325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90761300780767135188672883 136141951171150702783009325)
    ·
      refine ⟨51053231689181513543628497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136141951171150702783009325 51053231689181513543628497)
      ·
        refine ⟨38289923766886135157721373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51053231689181513543628497 38289923766886135157721373)
        ·
          refine ⟨14358721412582300684145515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38289923766886135157721373 14358721412582300684145515)
          ·
            refine ⟨21538082118873451026218273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14358721412582300684145515 21538082118873451026218273)
            ·
              refine ⟨16153561589155088269663705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21538082118873451026218273 16153561589155088269663705)
              ·
                refine ⟨12115171191866316202247779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16153561589155088269663705 12115171191866316202247779)
                ·
                  refine ⟨18172756787799474303371669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12115171191866316202247779 18172756787799474303371669)
                  ·
                    refine ⟨851847974428100357970547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18172756787799474303371669 851847974428100357970547)
                    ·
                      rfl

theorem cell23_4976904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 2, 1, 6].length) (baseStart_4976904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4976904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4976904 prefixEnd_4976904 := by exact prefixLift 4976904
  have htrace : WordTrace (prefixWord ++ tailWord_4976904) baseStart_4976904 baseEnd_4976904 := by
    simpa [prefixWord, tailWord_4976904, baseEnd_4976904] using wordTrace_append hprefix tailTrace_4976904
  have hstable : (prefixWord ++ tailWord_4976904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4976904).length < 2 ^ (prefixWord ++ tailWord_4976904).sum := by decide
  have hdescent : baseEnd_4976904 < baseStart_4976904 := by decide
  rcases family_descends (prefixWord ++ tailWord_4976904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4976928 : List Nat := [2, 1, 1, 5, 2, 1, 1, 3, 3, 2, 2]
def baseStart_4976928 : Nat := 118140960795 + 4976928 * 2 ^ 59
def prefixEnd_4976928 : Nat := 4983230072969 + 3 ^ 40 * 4976928 * 2
def baseEnd_4976928 : Nat := 2555556246820008980011531

theorem tailTrace_4976928 : CollatzResearch.WordTrace tailWord_4976928 prefixEnd_4976928 2555556246820008980011531 := by
  unfold tailWord_4976928
  simp only [CollatzResearch.WordTrace]
  refine ⟨90761738456723661238109719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121015651275631548317479625 90761738456723661238109719)
  ·
    refine ⟨136142607685085491857164579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90761738456723661238109719 136142607685085491857164579)
    ·
      refine ⟨204213911527628237785746869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136142607685085491857164579 204213911527628237785746869)
      ·
        refine ⟨19145054205715147292413769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 204213911527628237785746869 19145054205715147292413769)
        ·
          refine ⟨14358790654286360469310327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19145054205715147292413769 14358790654286360469310327)
          ·
            refine ⟨21538185981429540703965491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14358790654286360469310327 21538185981429540703965491)
            ·
              refine ⟨32307278972144311055948237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21538185981429540703965491 32307278972144311055948237)
              ·
                refine ⟨12115229614554116645980589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32307278972144311055948237 12115229614554116645980589)
                ·
                  refine ⟨4543211105457793742242721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12115229614554116645980589 4543211105457793742242721)
                  ·
                    refine ⟨3407408329093345306682041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4543211105457793742242721 3407408329093345306682041)
                    ·
                      refine ⟨2555556246820008980011531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3407408329093345306682041 2555556246820008980011531)
                      ·
                        rfl

theorem cell23_4976928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 3, 3, 2, 2].length) (baseStart_4976928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4976928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4976928 prefixEnd_4976928 := by exact prefixLift 4976928
  have htrace : WordTrace (prefixWord ++ tailWord_4976928) baseStart_4976928 baseEnd_4976928 := by
    simpa [prefixWord, tailWord_4976928, baseEnd_4976928] using wordTrace_append hprefix tailTrace_4976928
  have hstable : (prefixWord ++ tailWord_4976928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4976928).length < 2 ^ (prefixWord ++ tailWord_4976928).sum := by decide
  have hdescent : baseEnd_4976928 < baseStart_4976928 := by decide
  rcases family_descends (prefixWord ++ tailWord_4976928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4976938 : List Nat := [3, 1, 4, 2, 2, 2, 1, 1, 1, 6]
def baseStart_4976938 : Nat := 118140960795 + 4976938 * 2 ^ 59
def prefixEnd_4976938 : Nat := 4983230072969 + 3 ^ 40 * 4976938 * 2
def baseEnd_4976938 : Nat := 851853793875517980295495

theorem tailTrace_4976938 : CollatzResearch.WordTrace tailWord_4976938 prefixEnd_4976938 851853793875517980295495 := by
  unfold tailWord_4976938
  simp only [CollatzResearch.WordTrace]
  refine ⟨45380960410852773546020867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121015894428940729456055645 45380960410852773546020867)
  ·
    refine ⟨68071440616279160319031301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45380960410852773546020867 68071440616279160319031301)
    ·
      refine ⟨12763395115552342559818369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68071440616279160319031301 12763395115552342559818369)
      ·
        refine ⟨9572546336664256919863777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12763395115552342559818369 9572546336664256919863777)
        ·
          refine ⟨7179409752498192689897833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9572546336664256919863777 7179409752498192689897833)
          ·
            refine ⟨5384557314373644517423375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7179409752498192689897833 5384557314373644517423375)
            ·
              refine ⟨8076835971560466776135063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5384557314373644517423375 8076835971560466776135063)
              ·
                refine ⟨12115253957340700164202595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8076835971560466776135063 12115253957340700164202595)
                ·
                  refine ⟨18172880936011050246303893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12115253957340700164202595 18172880936011050246303893)
                  ·
                    refine ⟨851853793875517980295495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18172880936011050246303893 851853793875517980295495)
                    ·
                      rfl

theorem cell23_4976938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_4976938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4976938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4976938 prefixEnd_4976938 := by exact prefixLift 4976938
  have htrace : WordTrace (prefixWord ++ tailWord_4976938) baseStart_4976938 baseEnd_4976938 := by
    simpa [prefixWord, tailWord_4976938, baseEnd_4976938] using wordTrace_append hprefix tailTrace_4976938
  have hstable : (prefixWord ++ tailWord_4976938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4976938).length < 2 ^ (prefixWord ++ tailWord_4976938).sum := by decide
  have hdescent : baseEnd_4976938 < baseStart_4976938 := by decide
  rcases family_descends (prefixWord ++ tailWord_4976938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4976944 : List Nat := [2, 1, 1, 1, 2, 2, 2, 5, 1, 3, 3]
def baseStart_4976944 : Nat := 118140960795 + 4976944 * 2 ^ 59
def prefixEnd_4976944 : Nat := 4983230072969 + 3 ^ 40 * 4976944 * 2
def baseEnd_4976944 : Nat := 2555564462510480917411457

theorem tailTrace_4976944 : CollatzResearch.WordTrace tailWord_4976944 prefixEnd_4976944 2555564462510480917411457 := by
  unfold tailWord_4976944
  simp only [CollatzResearch.WordTrace]
  refine ⟨90762030240694678604400943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121016040320926238139201257 90762030240694678604400943)
  ·
    refine ⟨136143045361042017906601415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90762030240694678604400943 136143045361042017906601415)
    ·
      refine ⟨204214568041563026859902123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136143045361042017906601415 204214568041563026859902123)
      ·
        refine ⟨306321852062344540289853185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204214568041563026859902123 306321852062344540289853185)
        ·
          refine ⟨229741389046758405217389889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 306321852062344540289853185 229741389046758405217389889)
          ·
            refine ⟨172306041785068803913042417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 229741389046758405217389889 172306041785068803913042417)
            ·
              refine ⟨129229531338801602934781813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 172306041785068803913042417 129229531338801602934781813)
              ·
                refine ⟨12115268563012650275135795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 129229531338801602934781813 12115268563012650275135795)
                ·
                  refine ⟨18172902844518975412703693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12115268563012650275135795 18172902844518975412703693)
                  ·
                    refine ⟨6814838566694615779763885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18172902844518975412703693 6814838566694615779763885)
                    ·
                      refine ⟨2555564462510480917411457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6814838566694615779763885 2555564462510480917411457)
                      ·
                        rfl

theorem cell23_4976944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 5, 1, 3, 3].length) (baseStart_4976944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4976944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4976944 prefixEnd_4976944 := by exact prefixLift 4976944
  have htrace : WordTrace (prefixWord ++ tailWord_4976944) baseStart_4976944 baseEnd_4976944 := by
    simpa [prefixWord, tailWord_4976944, baseEnd_4976944] using wordTrace_append hprefix tailTrace_4976944
  have hstable : (prefixWord ++ tailWord_4976944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4976944).length < 2 ^ (prefixWord ++ tailWord_4976944).sum := by decide
  have hdescent : baseEnd_4976944 < baseStart_4976944 := by decide
  rcases family_descends (prefixWord ++ tailWord_4976944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4976948 : List Nat := [2, 5, 1, 1, 1, 2, 1, 4, 1, 2, 3]
def baseStart_4976948 : Nat := 118140960795 + 4976948 * 2 ^ 59
def prefixEnd_4976948 : Nat := 4983230072969 + 3 ^ 40 * 4976948 * 2
def baseEnd_4976948 : Nat := 2555566516433098901761439

theorem tailTrace_4976948 : CollatzResearch.WordTrace tailWord_4976948 prefixEnd_4976948 2555566516433098901761439 := by
  unfold tailWord_4976948
  simp only [CollatzResearch.WordTrace]
  refine ⟨90762103186687432945973749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121016137582249910594631665 90762103186687432945973749)
  ·
    refine ⟨8508947173751946838685039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 90762103186687432945973749 8508947173751946838685039)
    ·
      refine ⟨12763420760627920258027559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8508947173751946838685039 12763420760627920258027559)
      ·
        refine ⟨19145131140941880387041339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12763420760627920258027559 19145131140941880387041339)
        ·
          refine ⟨28717696711412820580562009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19145131140941880387041339 28717696711412820580562009)
          ·
            refine ⟨21538272533559615435421507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28717696711412820580562009 21538272533559615435421507)
            ·
              refine ⟨32307408800339423153132261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21538272533559615435421507 32307408800339423153132261)
              ·
                refine ⟨6057639150063641841212299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32307408800339423153132261 6057639150063641841212299)
                ·
                  refine ⟨9086458725095462761818449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6057639150063641841212299 9086458725095462761818449)
                  ·
                    refine ⟨6814844043821597071363837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9086458725095462761818449 6814844043821597071363837)
                    ·
                      refine ⟨2555566516433098901761439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6814844043821597071363837 2555566516433098901761439)
                      ·
                        rfl

theorem cell23_4976948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_4976948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4976948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4976948 prefixEnd_4976948 := by exact prefixLift 4976948
  have htrace : WordTrace (prefixWord ++ tailWord_4976948) baseStart_4976948 baseEnd_4976948 := by
    simpa [prefixWord, tailWord_4976948, baseEnd_4976948] using wordTrace_append hprefix tailTrace_4976948
  have hstable : (prefixWord ++ tailWord_4976948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4976948).length < 2 ^ (prefixWord ++ tailWord_4976948).sum := by decide
  have hdescent : baseEnd_4976948 < baseStart_4976948 := by decide
  rcases family_descends (prefixWord ++ tailWord_4976948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4977001 : List Nat := [1, 2, 1, 1, 1, 3, 4, 3, 1, 4, 2]
def baseStart_4977001 : Nat := 118140960795 + 4977001 * 2 ^ 59
def prefixEnd_4977001 : Nat := 4983230072969 + 3 ^ 40 * 4977001 * 2
def baseEnd_4977001 : Nat := 2555593730907787194398695

theorem tailTrace_4977001 : CollatzResearch.WordTrace tailWord_4977001 prefixEnd_4977001 2555593730907787194398695 := by
  unfold tailWord_4977001
  simp only [CollatzResearch.WordTrace]
  refine ⟨181526139442182855943626857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121017426294788570629084571 181526139442182855943626857)
  ·
    refine ⟨136144604581637141957720143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181526139442182855943626857 136144604581637141957720143)
    ·
      refine ⟨204216906872455712936580215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136144604581637141957720143 204216906872455712936580215)
      ·
        refine ⟨306325360308683569404870323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204216906872455712936580215 306325360308683569404870323)
        ·
          refine ⟨459488040463025354107305485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 306325360308683569404870323 459488040463025354107305485)
          ·
            refine ⟨172308015173634507790239557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 459488040463025354107305485 172308015173634507790239557)
            ·
              refine ⟨32307752845056470210669917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 172308015173634507790239557 32307752845056470210669917)
              ·
                refine ⟨12115407316896176329001219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32307752845056470210669917 12115407316896176329001219)
                ·
                  refine ⟨18173110975344264493501829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12115407316896176329001219 18173110975344264493501829)
                  ·
                    refine ⟨3407458307877049592531593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18173110975344264493501829 3407458307877049592531593)
                    ·
                      refine ⟨2555593730907787194398695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3407458307877049592531593 2555593730907787194398695)
                      ·
                        rfl

theorem cell23_4977001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 3, 1, 4, 2].length) (baseStart_4977001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4977001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4977001 prefixEnd_4977001 := by exact prefixLift 4977001
  have htrace : WordTrace (prefixWord ++ tailWord_4977001) baseStart_4977001 baseEnd_4977001 := by
    simpa [prefixWord, tailWord_4977001, baseEnd_4977001] using wordTrace_append hprefix tailTrace_4977001
  have hstable : (prefixWord ++ tailWord_4977001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4977001).length < 2 ^ (prefixWord ++ tailWord_4977001).sum := by decide
  have hdescent : baseEnd_4977001 < baseStart_4977001 := by decide
  rcases family_descends (prefixWord ++ tailWord_4977001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4977035 : List Nat := [1, 1, 1, 1, 4, 5, 2, 2, 2, 2, 2]
def baseStart_4977035 : Nat := 118140960795 + 4977035 * 2 ^ 59
def prefixEnd_4977035 : Nat := 4983230072969 + 3 ^ 40 * 4977035 * 2
def baseEnd_4977035 : Nat := 2555611189250040061373539

theorem tailTrace_4977035 : CollatzResearch.WordTrace tailWord_4977035 prefixEnd_4977035 2555611189250040061373539 := by
  unfold tailWord_4977035
  simp only [CollatzResearch.WordTrace]
  refine ⟨181527379524059679750364559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121018253016039786500243039 181527379524059679750364559)
  ·
    refine ⟨272291069286089519625546839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181527379524059679750364559 272291069286089519625546839)
    ·
      refine ⟨408436603929134279438320259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272291069286089519625546839 408436603929134279438320259)
      ·
        refine ⟨612654905893701419157480389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 408436603929134279438320259 612654905893701419157480389)
        ·
          refine ⟨114872794855069016092027573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 612654905893701419157480389 114872794855069016092027573)
          ·
            refine ⟨10769324517662720258627585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 114872794855069016092027573 10769324517662720258627585)
            ·
              refine ⟨8076993388247040193970689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10769324517662720258627585 8076993388247040193970689)
              ·
                refine ⟨6057745041185280145478017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8076993388247040193970689 6057745041185280145478017)
                ·
                  refine ⟨4543308780888960109108513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6057745041185280145478017 4543308780888960109108513)
                  ·
                    refine ⟨3407481585666720081831385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4543308780888960109108513 3407481585666720081831385)
                    ·
                      refine ⟨2555611189250040061373539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3407481585666720081831385 2555611189250040061373539)
                      ·
                        rfl

theorem cell23_4977035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 2, 2, 2, 2].length) (baseStart_4977035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4977035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4977035 prefixEnd_4977035 := by exact prefixLift 4977035
  have htrace : WordTrace (prefixWord ++ tailWord_4977035) baseStart_4977035 baseEnd_4977035 := by
    simpa [prefixWord, tailWord_4977035, baseEnd_4977035] using wordTrace_append hprefix tailTrace_4977035
  have hstable : (prefixWord ++ tailWord_4977035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4977035).length < 2 ^ (prefixWord ++ tailWord_4977035).sum := by decide
  have hdescent : baseEnd_4977035 < baseStart_4977035 := by decide
  rcases family_descends (prefixWord ++ tailWord_4977035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4977061 : List Nat := [1, 3, 1, 2, 1, 1, 3, 2, 2, 5, 2]
def baseStart_4977061 : Nat := 118140960795 + 4977061 * 2 ^ 59
def prefixEnd_4977061 : Nat := 4983230072969 + 3 ^ 40 * 4977061 * 2
def baseEnd_4977061 : Nat := 2555624539747056959648419

theorem tailTrace_4977061 : CollatzResearch.WordTrace tailWord_4977061 prefixEnd_4977061 2555624539747056959648419 := by
  unfold tailWord_4977061
  simp only [CollatzResearch.WordTrace]
  refine ⟨181528327821965486190811037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121018885214643657460540691 181528327821965486190811037)
  ·
    refine ⟨68073122933237057321554139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181528327821965486190811037 68073122933237057321554139)
    ·
      refine ⟨102109684399855585982331209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68073122933237057321554139 102109684399855585982331209)
      ·
        refine ⟨76582263299891689486748407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102109684399855585982331209 76582263299891689486748407)
        ·
          refine ⟨114873394949837534230122611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76582263299891689486748407 114873394949837534230122611)
          ·
            refine ⟨172310092424756301345183917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114873394949837534230122611 172310092424756301345183917)
            ·
              refine ⟨64616284659283613004443969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 172310092424756301345183917 64616284659283613004443969)
              ·
                refine ⟨48462213494462709753332977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64616284659283613004443969 48462213494462709753332977)
                ·
                  refine ⟨36346660120847032314999733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48462213494462709753332977 36346660120847032314999733)
                  ·
                    refine ⟨3407499386329409279531225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36346660120847032314999733 3407499386329409279531225)
                    ·
                      refine ⟨2555624539747056959648419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3407499386329409279531225 2555624539747056959648419)
                      ·
                        rfl

theorem cell23_4977061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 5, 2].length) (baseStart_4977061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4977061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4977061 prefixEnd_4977061 := by exact prefixLift 4977061
  have htrace : WordTrace (prefixWord ++ tailWord_4977061) baseStart_4977061 baseEnd_4977061 := by
    simpa [prefixWord, tailWord_4977061, baseEnd_4977061] using wordTrace_append hprefix tailTrace_4977061
  have hstable : (prefixWord ++ tailWord_4977061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4977061).length < 2 ^ (prefixWord ++ tailWord_4977061).sum := by decide
  have hdescent : baseEnd_4977061 < baseStart_4977061 := by decide
  rcases family_descends (prefixWord ++ tailWord_4977061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4977104 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 4]
def baseStart_4977104 : Nat := 118140960795 + 4977104 * 2 ^ 59
def prefixEnd_4977104 : Nat := 4983230072969 + 3 ^ 40 * 4977104 * 2
def baseEnd_4977104 : Nat := 2555646619415200291410721

theorem tailTrace_4977104 : CollatzResearch.WordTrace tailWord_4977104 prefixEnd_4977104 2555646619415200291410721 := by
  unfold tailWord_4977104
  simp only [CollatzResearch.WordTrace]
  refine ⟨90764948080404852267313183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121019930773873136356417577 90764948080404852267313183)
  ·
    refine ⟨136147422120607278400969775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90764948080404852267313183 136147422120607278400969775)
    ·
      refine ⟨204221133180910917601454663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136147422120607278400969775 204221133180910917601454663)
      ·
        refine ⟨306331699771366376402181995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204221133180910917601454663 306331699771366376402181995)
        ·
          refine ⟨459497549657049564603272993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 306331699771366376402181995 459497549657049564603272993)
          ·
            refine ⟨344623162242787173452454745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 459497549657049564603272993 344623162242787173452454745)
            ·
              refine ⟨258467371682090380089341059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 344623162242787173452454745 258467371682090380089341059)
              ·
                refine ⟨387701057523135570134011589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 258467371682090380089341059 387701057523135570134011589)
                ·
                  refine ⟨72693948285587919400127173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 387701057523135570134011589 72693948285587919400127173)
                  ·
                    refine ⟨13630115303547734887523845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 72693948285587919400127173 13630115303547734887523845)
                    ·
                      refine ⟨2555646619415200291410721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13630115303547734887523845 2555646619415200291410721)
                      ·
                        rfl

theorem cell23_4977104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 4].length) (baseStart_4977104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4977104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4977104 prefixEnd_4977104 := by exact prefixLift 4977104
  have htrace : WordTrace (prefixWord ++ tailWord_4977104) baseStart_4977104 baseEnd_4977104 := by
    simpa [prefixWord, tailWord_4977104, baseEnd_4977104] using wordTrace_append hprefix tailTrace_4977104
  have hstable : (prefixWord ++ tailWord_4977104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4977104).length < 2 ^ (prefixWord ++ tailWord_4977104).sum := by decide
  have hdescent : baseEnd_4977104 < baseStart_4977104 := by decide
  rcases family_descends (prefixWord ++ tailWord_4977104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4977124 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 2, 1, 9]
def baseStart_4977124 : Nat := 118140960795 + 4977124 * 2 ^ 59
def prefixEnd_4977124 : Nat := 4983230072969 + 3 ^ 40 * 4977124 * 2
def baseEnd_4977124 : Nat := 2555656889028290213160629

theorem tailTrace_4977124 : CollatzResearch.WordTrace tailWord_4977124 prefixEnd_4977124 2555656889028290213160629 := by
  unfold tailWord_4977124
  simp only [CollatzResearch.WordTrace]
  refine ⟨90765312810368623975177213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121020417080491498633569617 90765312810368623975177213)
  ·
    refine ⟨34036992303888233990691455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90765312810368623975177213 34036992303888233990691455)
    ·
      refine ⟨51055488455832350986037183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34036992303888233990691455 51055488455832350986037183)
      ·
        refine ⟨76583232683748526479055775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51055488455832350986037183 76583232683748526479055775)
        ·
          refine ⟨114874849025622789718583663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76583232683748526479055775 114874849025622789718583663)
          ·
            refine ⟨172312273538434184577875495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114874849025622789718583663 172312273538434184577875495)
            ·
              refine ⟨258468410307651276866813243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172312273538434184577875495 258468410307651276866813243)
              ·
                refine ⟨387702615461476915300219865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 258468410307651276866813243 387702615461476915300219865)
                ·
                  refine ⟨290776961596107686475164899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 387702615461476915300219865 290776961596107686475164899)
                  ·
                    refine ⟨436165442394161529712747349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 290776961596107686475164899 436165442394161529712747349)
                    ·
                      refine ⟨2555656889028290213160629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 436165442394161529712747349 2555656889028290213160629)
                      ·
                        rfl

theorem cell23_4977124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_4977124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4977124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4977124 prefixEnd_4977124 := by exact prefixLift 4977124
  have htrace : WordTrace (prefixWord ++ tailWord_4977124) baseStart_4977124 baseEnd_4977124 := by
    simpa [prefixWord, tailWord_4977124, baseEnd_4977124] using wordTrace_append hprefix tailTrace_4977124
  have hstable : (prefixWord ++ tailWord_4977124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4977124).length < 2 ^ (prefixWord ++ tailWord_4977124).sum := by decide
  have hdescent : baseEnd_4977124 < baseStart_4977124 := by decide
  rcases family_descends (prefixWord ++ tailWord_4977124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4977178 : List Nat := [3, 1, 1, 3, 1, 1, 5, 2, 1, 5]
def baseStart_4977178 : Nat := 118140960795 + 4977178 * 2 ^ 59
def prefixEnd_4977178 : Nat := 4983230072969 + 3 ^ 40 * 4977178 * 2
def baseEnd_4977178 : Nat := 851894872327877667295127

theorem tailTrace_4977178 : CollatzResearch.WordTrace tailWord_4977178 prefixEnd_4977178 851894872327877667295127 := by
  unfold tailWord_4977178
  simp only [CollatzResearch.WordTrace]
  refine ⟨45383148790635403793205047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121021730108361076781880125 45383148790635403793205047)
  ·
    refine ⟨68074723185953105689807571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45383148790635403793205047 68074723185953105689807571)
    ·
      refine ⟨102112084778929658534711357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68074723185953105689807571 102112084778929658534711357)
      ·
        refine ⟨38292031792098621950516759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102112084778929658534711357 38292031792098621950516759)
        ·
          refine ⟨57438047688147932925775139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38292031792098621950516759 57438047688147932925775139)
          ·
            refine ⟨86157071532221899388662709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57438047688147932925775139 86157071532221899388662709)
            ·
              refine ⟨8077225456145803067687129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 86157071532221899388662709 8077225456145803067687129)
              ·
                refine ⟨6057919092109352300765347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8077225456145803067687129 6057919092109352300765347)
                ·
                  refine ⟨9086878638164028451148021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6057919092109352300765347 9086878638164028451148021)
                  ·
                    refine ⟨851894872327877667295127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9086878638164028451148021 851894872327877667295127)
                    ·
                      rfl

theorem cell23_4977178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 2, 1, 5].length) (baseStart_4977178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4977178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4977178 prefixEnd_4977178 := by exact prefixLift 4977178
  have htrace : WordTrace (prefixWord ++ tailWord_4977178) baseStart_4977178 baseEnd_4977178 := by
    simpa [prefixWord, tailWord_4977178, baseEnd_4977178] using wordTrace_append hprefix tailTrace_4977178
  have hstable : (prefixWord ++ tailWord_4977178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4977178).length < 2 ^ (prefixWord ++ tailWord_4977178).sum := by decide
  have hdescent : baseEnd_4977178 < baseStart_4977178 := by decide
  rcases family_descends (prefixWord ++ tailWord_4977178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4977185 : List Nat := [1, 2, 3, 2, 2, 1, 4, 1, 2, 3, 2]
def baseStart_4977185 : Nat := 118140960795 + 4977185 * 2 ^ 59
def prefixEnd_4977185 : Nat := 4983230072969 + 3 ^ 40 * 4977185 * 2
def baseEnd_4977185 : Nat := 2555688211348214474497849

theorem tailTrace_4977185 : CollatzResearch.WordTrace tailWord_4977185 prefixEnd_4977185 2555688211348214474497849 := by
  unfold tailWord_4977185
  simp only [CollatzResearch.WordTrace]
  refine ⟨181532850473516255368325009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121021900315677503578883339 181532850473516255368325009)
  ·
    refine ⟨136149637855137191526243757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181532850473516255368325009 136149637855137191526243757)
    ·
      refine ⟨51056114195676446822341409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136149637855137191526243757 51056114195676446822341409)
      ·
        refine ⟨38292085646757335116756057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51056114195676446822341409 38292085646757335116756057)
        ·
          refine ⟨28719064235068001337567043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38292085646757335116756057 28719064235068001337567043)
          ·
            refine ⟨43078596352602002006350565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28719064235068001337567043 43078596352602002006350565)
            ·
              refine ⟨8077236816112875376190731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43078596352602002006350565 8077236816112875376190731)
              ·
                refine ⟨12115855224169313064286097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8077236816112875376190731 12115855224169313064286097)
                ·
                  refine ⟨9086891418126984798214573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12115855224169313064286097 9086891418126984798214573)
                  ·
                    refine ⟨3407584281797619299330465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9086891418126984798214573 3407584281797619299330465)
                    ·
                      refine ⟨2555688211348214474497849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3407584281797619299330465 2555688211348214474497849)
                      ·
                        rfl

theorem cell23_4977185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 1, 2, 3, 2].length) (baseStart_4977185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4977185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4977185 prefixEnd_4977185 := by exact prefixLift 4977185
  have htrace : WordTrace (prefixWord ++ tailWord_4977185) baseStart_4977185 baseEnd_4977185 := by
    simpa [prefixWord, tailWord_4977185, baseEnd_4977185] using wordTrace_append hprefix tailTrace_4977185
  have hstable : (prefixWord ++ tailWord_4977185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4977185).length < 2 ^ (prefixWord ++ tailWord_4977185).sum := by decide
  have hdescent : baseEnd_4977185 < baseStart_4977185 := by decide
  rcases family_descends (prefixWord ++ tailWord_4977185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4977215 : List Nat := [1, 1, 2, 2, 3, 2, 2, 3, 3, 2, 2]
def baseStart_4977215 : Nat := 118140960795 + 4977215 * 2 ^ 59
def prefixEnd_4977215 : Nat := 4983230072969 + 3 ^ 40 * 4977215 * 2
def baseEnd_4977215 : Nat := 2555703615767849357122711

theorem tailTrace_4977215 : CollatzResearch.WordTrace tailWord_4977215 prefixEnd_4977215 2555703615767849357122711 := by
  unfold tailWord_4977215
  simp only [CollatzResearch.WordTrace]
  refine ⟨181533944663407570491917099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121022629775605046994611399 181533944663407570491917099)
  ·
    refine ⟨272300916995111355737875649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181533944663407570491917099 272300916995111355737875649)
    ·
      refine ⟨204225687746333516803406737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 272300916995111355737875649 204225687746333516803406737)
      ·
        refine ⟨153169265809750137602555053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204225687746333516803406737 153169265809750137602555053)
        ·
          refine ⟨57438474678656301600958145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 153169265809750137602555053 57438474678656301600958145)
          ·
            refine ⟨43078856008992226200718609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57438474678656301600958145 43078856008992226200718609)
            ·
              refine ⟨32309142006744169650538957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43078856008992226200718609 32309142006744169650538957)
              ·
                refine ⟨12115928252529063618952109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32309142006744169650538957 12115928252529063618952109)
                ·
                  refine ⟨4543473094698398857107041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12115928252529063618952109 4543473094698398857107041)
                  ·
                    refine ⟨3407604821023799142830281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4543473094698398857107041 3407604821023799142830281)
                    ·
                      refine ⟨2555703615767849357122711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3407604821023799142830281 2555703615767849357122711)
                      ·
                        rfl

theorem cell23_4977215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 3, 3, 2, 2].length) (baseStart_4977215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4977215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4977215 prefixEnd_4977215 := by exact prefixLift 4977215
  have htrace : WordTrace (prefixWord ++ tailWord_4977215) baseStart_4977215 baseEnd_4977215 := by
    simpa [prefixWord, tailWord_4977215, baseEnd_4977215] using wordTrace_append hprefix tailTrace_4977215
  have hstable : (prefixWord ++ tailWord_4977215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4977215).length < 2 ^ (prefixWord ++ tailWord_4977215).sum := by decide
  have hdescent : baseEnd_4977215 < baseStart_4977215 := by decide
  rcases family_descends (prefixWord ++ tailWord_4977215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4977221 : List Nat := [1, 3, 1, 1, 1, 5, 3, 8]
def baseStart_4977221 : Nat := 118140960795 + 4977221 * 2 ^ 59
def prefixEnd_4977221 : Nat := 4983230072969 + 3 ^ 40 * 4977221 * 2
def baseEnd_4977221 : Nat := 94655803579695419764729

theorem tailTrace_4977221 : CollatzResearch.WordTrace tailWord_4977221 prefixEnd_4977221 94655803579695419764729 := by
  unfold tailWord_4977221
  simp only [CollatzResearch.WordTrace]
  refine ⟨181534163501385833516635517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121022775667590555677757011 181534163501385833516635517)
  ·
    refine ⟨68075311313019687568738319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181534163501385833516635517 68075311313019687568738319)
    ·
      refine ⟨102112966969529531353107479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68075311313019687568738319 102112966969529531353107479)
      ·
        refine ⟨153169450454294297029661219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102112966969529531353107479 153169450454294297029661219)
        ·
          refine ⟨229754175681441445544491829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153169450454294297029661219 229754175681441445544491829)
          ·
            refine ⟨21539453970135135519796109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 229754175681441445544491829 21539453970135135519796109)
            ·
              refine ⟨8077295238800675819923541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21539453970135135519796109 8077295238800675819923541)
              ·
                refine ⟨94655803579695419764729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8077295238800675819923541 94655803579695419764729)
                ·
                  rfl

theorem cell23_4977221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 8].length) (baseStart_4977221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4977221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4977221 prefixEnd_4977221 := by exact prefixLift 4977221
  have htrace : WordTrace (prefixWord ++ tailWord_4977221) baseStart_4977221 baseEnd_4977221 := by
    simpa [prefixWord, tailWord_4977221, baseEnd_4977221] using wordTrace_append hprefix tailTrace_4977221
  have hstable : (prefixWord ++ tailWord_4977221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4977221).length < 2 ^ (prefixWord ++ tailWord_4977221).sum := by decide
  have hdescent : baseEnd_4977221 < baseStart_4977221 := by decide
  rcases family_descends (prefixWord ++ tailWord_4977221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4977228 : List Nat := [2, 2, 1, 3, 1, 2, 4, 1, 1, 2, 4]
def baseStart_4977228 : Nat := 118140960795 + 4977228 * 2 ^ 59
def prefixEnd_4977228 : Nat := 4983230072969 + 3 ^ 40 * 4977228 * 2
def baseEnd_4977228 : Nat := 2555710291016357806260151

theorem tailTrace_4977228 : CollatzResearch.WordTrace tailWord_4977228 prefixEnd_4977228 2555710291016357806260151 := by
  unfold tailWord_4977228
  simp only [CollatzResearch.WordTrace]
  refine ⟨90767209406180236856070169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121022945874906982474760225 90767209406180236856070169)
  ·
    refine ⟨68075407054635177642052627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90767209406180236856070169 68075407054635177642052627)
    ·
      refine ⟨102113110581952766463078941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68075407054635177642052627 102113110581952766463078941)
      ·
        refine ⟨38292416468232287423654603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102113110581952766463078941 38292416468232287423654603)
        ·
          refine ⟨57438624702348431135481905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38292416468232287423654603 57438624702348431135481905)
          ·
            refine ⟨43078968526761323351611429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57438624702348431135481905 43078968526761323351611429)
            ·
              refine ⟨8077306598767748128427143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43078968526761323351611429 8077306598767748128427143)
              ·
                refine ⟨12115959898151622192640715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8077306598767748128427143 12115959898151622192640715)
                ·
                  refine ⟨18173939847227433288961073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12115959898151622192640715 18173939847227433288961073)
                  ·
                    refine ⟨13630454885420574966720805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18173939847227433288961073 13630454885420574966720805)
                    ·
                      refine ⟨2555710291016357806260151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13630454885420574966720805 2555710291016357806260151)
                      ·
                        rfl

theorem cell23_4977228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 1, 1, 2, 4].length) (baseStart_4977228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4977228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4977228 prefixEnd_4977228 := by exact prefixLift 4977228
  have htrace : WordTrace (prefixWord ++ tailWord_4977228) baseStart_4977228 baseEnd_4977228 := by
    simpa [prefixWord, tailWord_4977228, baseEnd_4977228] using wordTrace_append hprefix tailTrace_4977228
  have hstable : (prefixWord ++ tailWord_4977228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4977228).length < 2 ^ (prefixWord ++ tailWord_4977228).sum := by decide
  have hdescent : baseEnd_4977228 < baseStart_4977228 := by decide
  rcases family_descends (prefixWord ++ tailWord_4977228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4977248 : List Nat := [2, 1, 1, 3, 2, 1, 4, 2, 1, 3, 3]
def baseStart_4977248 : Nat := 118140960795 + 4977248 * 2 ^ 59
def prefixEnd_4977248 : Nat := 4983230072969 + 3 ^ 40 * 4977248 * 2
def baseEnd_4977248 : Nat := 2555720560629447728010059

theorem tailTrace_4977248 : CollatzResearch.WordTrace tailWord_4977248 prefixEnd_4977248 2555720560629447728010059 := by
  unfold tailWord_4977248
  simp only [CollatzResearch.WordTrace]
  refine ⟨90767574136144008563934199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121023432181525344751912265 90767574136144008563934199)
  ·
    refine ⟨136151361204216012845901299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90767574136144008563934199 136151361204216012845901299)
    ·
      refine ⟨204227041806324019268851949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136151361204216012845901299 204227041806324019268851949)
      ·
        refine ⟨76585140677371507225819481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 204227041806324019268851949 76585140677371507225819481)
        ·
          refine ⟨57438855508028630419364611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76585140677371507225819481 57438855508028630419364611)
          ·
            refine ⟨86158283262042945629046917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57438855508028630419364611 86158283262042945629046917)
            ·
              refine ⟨16154678111633052305446297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86158283262042945629046917 16154678111633052305446297)
              ·
                refine ⟨12116008583724789229084723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16154678111633052305446297 12116008583724789229084723)
                ·
                  refine ⟨18174012875587183843627085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12116008583724789229084723 18174012875587183843627085)
                  ·
                    refine ⟨6815254828345193941360157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18174012875587183843627085 6815254828345193941360157)
                    ·
                      refine ⟨2555720560629447728010059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6815254828345193941360157 2555720560629447728010059)
                      ·
                        rfl

theorem cell23_4977248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 2, 1, 3, 3].length) (baseStart_4977248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4977248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4977248 prefixEnd_4977248 := by exact prefixLift 4977248
  have htrace : WordTrace (prefixWord ++ tailWord_4977248) baseStart_4977248 baseEnd_4977248 := by
    simpa [prefixWord, tailWord_4977248, baseEnd_4977248] using wordTrace_append hprefix tailTrace_4977248
  have hstable : (prefixWord ++ tailWord_4977248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4977248).length < 2 ^ (prefixWord ++ tailWord_4977248).sum := by decide
  have hdescent : baseEnd_4977248 < baseStart_4977248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4977248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4977249 : List Nat := [1, 2, 3, 1, 1, 5, 2, 3, 1, 2, 2]
def baseStart_4977249 : Nat := 118140960795 + 4977249 * 2 ^ 59
def prefixEnd_4977249 : Nat := 4983230072969 + 3 ^ 40 * 4977249 * 2
def baseEnd_4977249 : Nat := 2555721074110102224097555

theorem tailTrace_4977249 : CollatzResearch.WordTrace tailWord_4977249 prefixEnd_4977249 2555721074110102224097555 := by
  unfold tailWord_4977249
  simp only [CollatzResearch.WordTrace]
  refine ⟨181535184745284394298654801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121023456496856262865769867 181535184745284394298654801)
  ·
    refine ⟨136151388558963295723991101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181535184745284394298654801 136151388558963295723991101)
    ·
      refine ⟨51056770709611235896496663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136151388558963295723991101 51056770709611235896496663)
      ·
        refine ⟨76585156064416853844744995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51056770709611235896496663 76585156064416853844744995)
        ·
          refine ⟨114877734096625280767117493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76585156064416853844744995 114877734096625280767117493)
          ·
            refine ⟨10769787571558620071917265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 114877734096625280767117493 10769787571558620071917265)
            ·
              refine ⟨8077340678668965053937949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10769787571558620071917265 8077340678668965053937949)
              ·
                refine ⟨3029002754500861895226731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8077340678668965053937949 3029002754500861895226731)
                ·
                  refine ⟨4543504131751292842840097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3029002754500861895226731 4543504131751292842840097)
                  ·
                    refine ⟨3407628098813469632130073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4543504131751292842840097 3407628098813469632130073)
                    ·
                      refine ⟨2555721074110102224097555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3407628098813469632130073 2555721074110102224097555)
                      ·
                        rfl

theorem cell23_4977249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 3, 1, 2, 2].length) (baseStart_4977249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4977249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4977249 prefixEnd_4977249 := by exact prefixLift 4977249
  have htrace : WordTrace (prefixWord ++ tailWord_4977249) baseStart_4977249 baseEnd_4977249 := by
    simpa [prefixWord, tailWord_4977249, baseEnd_4977249] using wordTrace_append hprefix tailTrace_4977249
  have hstable : (prefixWord ++ tailWord_4977249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4977249).length < 2 ^ (prefixWord ++ tailWord_4977249).sum := by decide
  have hdescent : baseEnd_4977249 < baseStart_4977249 := by decide
  rcases family_descends (prefixWord ++ tailWord_4977249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4977271 : List Nat := [1, 1, 3, 1, 1, 3, 2, 1, 1, 5, 4]
def baseStart_4977271 : Nat := 118140960795 + 4977271 * 2 ^ 59
def prefixEnd_4977271 : Nat := 4983230072969 + 3 ^ 40 * 4977271 * 2
def baseEnd_4977271 : Nat := 2555732370684501138022453

theorem tailTrace_4977271 : CollatzResearch.WordTrace tailWord_4977271 prefixEnd_4977271 2555732370684501138022453 := by
  unfold tailWord_4977271
  simp only [CollatzResearch.WordTrace]
  refine ⟨181535987151204692055955667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121023991434136461370637111 181535987151204692055955667)
  ·
    refine ⟨272303980726807038083933501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181535987151204692055955667 272303980726807038083933501)
    ·
      refine ⟨102113992772552639281475063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 272303980726807038083933501 102113992772552639281475063)
      ·
        refine ⟨153170989158828958922212595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102113992772552639281475063 153170989158828958922212595)
        ·
          refine ⟨229756483738243438383318893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153170989158828958922212595 229756483738243438383318893)
          ·
            refine ⟨86158681401841289393744585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 229756483738243438383318893 86158681401841289393744585)
            ·
              refine ⟨64619011051380967045308439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86158681401841289393744585 64619011051380967045308439)
              ·
                refine ⟨96928516577071450567962659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64619011051380967045308439 96928516577071450567962659)
                ·
                  refine ⟨145392774865607175851943989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96928516577071450567962659 145392774865607175851943989)
                  ·
                    refine ⟨13630572643650672736119749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 145392774865607175851943989 13630572643650672736119749)
                    ·
                      refine ⟨2555732370684501138022453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13630572643650672736119749 2555732370684501138022453)
                      ·
                        rfl

theorem cell23_4977271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 5, 4].length) (baseStart_4977271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4977271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4977271 prefixEnd_4977271 := by exact prefixLift 4977271
  have htrace : WordTrace (prefixWord ++ tailWord_4977271) baseStart_4977271 baseEnd_4977271 := by
    simpa [prefixWord, tailWord_4977271, baseEnd_4977271] using wordTrace_append hprefix tailTrace_4977271
  have hstable : (prefixWord ++ tailWord_4977271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4977271).length < 2 ^ (prefixWord ++ tailWord_4977271).sum := by decide
  have hdescent : baseEnd_4977271 < baseStart_4977271 := by decide
  rcases family_descends (prefixWord ++ tailWord_4977271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4977305 : List Nat := [1, 2, 1, 2, 1, 2, 3, 1, 6, 2, 2]
def baseStart_4977305 : Nat := 118140960795 + 4977305 * 2 ^ 59
def prefixEnd_4977305 : Nat := 4983230072969 + 3 ^ 40 * 4977305 * 2
def baseEnd_4977305 : Nat := 2555749829026754004997297

theorem tailTrace_4977305 : CollatzResearch.WordTrace tailWord_4977305 prefixEnd_4977305 2555749829026754004997297 := by
  unfold tailWord_4977305
  simp only [CollatzResearch.WordTrace]
  refine ⟨181537227233081515862693369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121024818155387677241795579 181537227233081515862693369)
  ·
    refine ⟨136152920424811136897020027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181537227233081515862693369 136152920424811136897020027)
    ·
      refine ⟨204229380637216705345530041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136152920424811136897020027 204229380637216705345530041)
      ·
        refine ⟨153172035477912529009147531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204229380637216705345530041 153172035477912529009147531)
        ·
          refine ⟨229758053216868793513721297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153172035477912529009147531 229758053216868793513721297)
          ·
            refine ⟨172318539912651595135290973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 229758053216868793513721297 172318539912651595135290973)
            ·
              refine ⟨64619452467244348175734115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 172318539912651595135290973 64619452467244348175734115)
              ·
                refine ⟨96929178700866522263601173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64619452467244348175734115 96929178700866522263601173)
                ·
                  refine ⟨4543555251603118231106305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 96929178700866522263601173 4543555251603118231106305)
                  ·
                    refine ⟨3407666438702338673329729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4543555251603118231106305 3407666438702338673329729)
                    ·
                      refine ⟨2555749829026754004997297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3407666438702338673329729 2555749829026754004997297)
                      ·
                        rfl

theorem cell23_4977305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 6, 2, 2].length) (baseStart_4977305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4977305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4977305 prefixEnd_4977305 := by exact prefixLift 4977305
  have htrace : WordTrace (prefixWord ++ tailWord_4977305) baseStart_4977305 baseEnd_4977305 := by
    simpa [prefixWord, tailWord_4977305, baseEnd_4977305] using wordTrace_append hprefix tailTrace_4977305
  have hstable : (prefixWord ++ tailWord_4977305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4977305).length < 2 ^ (prefixWord ++ tailWord_4977305).sum := by decide
  have hdescent : baseEnd_4977305 < baseStart_4977305 := by decide
  rcases family_descends (prefixWord ++ tailWord_4977305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4977308 : List Nat := [2, 2, 3, 2, 2, 1, 1, 1, 1, 3, 5]
def baseStart_4977308 : Nat := 118140960795 + 4977308 * 2 ^ 59
def prefixEnd_4977308 : Nat := 4983230072969 + 3 ^ 40 * 4977308 * 2
def baseEnd_4977308 : Nat := 2555751369468717493259783

theorem tailTrace_4977308 : CollatzResearch.WordTrace tailWord_4977308 prefixEnd_4977308 2555751369468717493259783 := by
  unfold tailWord_4977308
  simp only [CollatzResearch.WordTrace]
  refine ⟨90768668326035323687526289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121024891101380431583368385 90768668326035323687526289)
  ·
    refine ⟨68076501244526492765644717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90768668326035323687526289 68076501244526492765644717)
    ·
      refine ⟨25528687966697434787116769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68076501244526492765644717 25528687966697434787116769)
      ·
        refine ⟨19146515975023076090337577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25528687966697434787116769 19146515975023076090337577)
        ·
          refine ⟨14359886981267307067753183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19146515975023076090337577 14359886981267307067753183)
          ·
            refine ⟨21539830471900960601629775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14359886981267307067753183 21539830471900960601629775)
            ·
              refine ⟨32309745707851440902444663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21539830471900960601629775 32309745707851440902444663)
              ·
                refine ⟨48464618561777161353666995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32309745707851440902444663 48464618561777161353666995)
                ·
                  refine ⟨72696927842665742030500493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48464618561777161353666995 72696927842665742030500493)
                  ·
                    refine ⟨27261347940999653261437685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 72696927842665742030500493 27261347940999653261437685)
                    ·
                      refine ⟨2555751369468717493259783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27261347940999653261437685 2555751369468717493259783)
                      ·
                        rfl

theorem cell23_4977308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_4977308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4977308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4977308 prefixEnd_4977308 := by exact prefixLift 4977308
  have htrace : WordTrace (prefixWord ++ tailWord_4977308) baseStart_4977308 baseEnd_4977308 := by
    simpa [prefixWord, tailWord_4977308, baseEnd_4977308] using wordTrace_append hprefix tailTrace_4977308
  have hstable : (prefixWord ++ tailWord_4977308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4977308).length < 2 ^ (prefixWord ++ tailWord_4977308).sum := by decide
  have hdescent : baseEnd_4977308 < baseStart_4977308 := by decide
  rcases family_descends (prefixWord ++ tailWord_4977308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4977338 : List Nat := [3, 1, 1, 1, 2, 3, 2, 1, 1, 5, 3]
def baseStart_4977338 : Nat := 118140960795 + 4977338 * 2 ^ 59
def prefixEnd_4977338 : Nat := 4983230072969 + 3 ^ 40 * 4977338 * 2
def baseEnd_4977338 : Nat := 2555766773888352375884645

theorem tailTrace_4977338 : CollatzResearch.WordTrace tailWord_4977338 prefixEnd_4977338 2555766773888352375884645 := by
  unfold tailWord_4977338
  simp only [CollatzResearch.WordTrace]
  refine ⟨45384607710490490624661167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 121025620561307974999096445 45384607710490490624661167)
  ·
    refine ⟨68076911565735735936991751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45384607710490490624661167 68076911565735735936991751)
    ·
      refine ⟨102115367348603603905487627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68076911565735735936991751 102115367348603603905487627)
      ·
        refine ⟨153173051022905405858231441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102115367348603603905487627 153173051022905405858231441)
        ·
          refine ⟨114879788267179054393673581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153173051022905405858231441 114879788267179054393673581)
          ·
            refine ⟨43079920600192145397627593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114879788267179054393673581 43079920600192145397627593)
            ·
              refine ⟨32309940450144109048220695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43079920600192145397627593 32309940450144109048220695)
              ·
                refine ⟨48464910675216163572331043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32309940450144109048220695 48464910675216163572331043)
                ·
                  refine ⟨72697366012824245358496565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48464910675216163572331043 72697366012824245358496565)
                  ·
                    refine ⟨6815378063702273002359053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 72697366012824245358496565 6815378063702273002359053)
                    ·
                      refine ⟨2555766773888352375884645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6815378063702273002359053 2555766773888352375884645)
                      ·
                        rfl

theorem cell23_4977338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 1, 5, 3].length) (baseStart_4977338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4977338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4977338 prefixEnd_4977338 := by exact prefixLift 4977338
  have htrace : WordTrace (prefixWord ++ tailWord_4977338) baseStart_4977338 baseEnd_4977338 := by
    simpa [prefixWord, tailWord_4977338, baseEnd_4977338] using wordTrace_append hprefix tailTrace_4977338
  have hstable : (prefixWord ++ tailWord_4977338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4977338).length < 2 ^ (prefixWord ++ tailWord_4977338).sum := by decide
  have hdescent : baseEnd_4977338 < baseStart_4977338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4977338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4977368 : List Nat := [2, 1, 2, 2, 3, 2, 1, 2, 1, 2, 5]
def baseStart_4977368 : Nat := 118140960795 + 4977368 * 2 ^ 59
def prefixEnd_4977368 : Nat := 4983230072969 + 3 ^ 40 * 4977368 * 2
def baseEnd_4977368 : Nat := 2555782178307987258509507

theorem tailTrace_4977368 : CollatzResearch.WordTrace tailWord_4977368 prefixEnd_4977368 2555782178307987258509507 := by
  unfold tailWord_4977368
  simp only [CollatzResearch.WordTrace]
  refine ⟨90769762515926638811118379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 121026350021235518414824505 90769762515926638811118379)
  ·
    refine ⟨136154643773889958216677569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90769762515926638811118379 136154643773889958216677569)
    ·
      refine ⟨102115982830417468662508177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136154643773889958216677569 102115982830417468662508177)
      ·
        refine ⟨76586987122813101496881133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102115982830417468662508177 76586987122813101496881133)
        ·
          refine ⟨28720120171054913061330425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76586987122813101496881133 28720120171054913061330425)
          ·
            refine ⟨21540090128291184795997819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28720120171054913061330425 21540090128291184795997819)
            ·
              refine ⟨32310135192436777193996729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21540090128291184795997819 32310135192436777193996729)
              ·
                refine ⟨24232601394327582895497547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32310135192436777193996729 24232601394327582895497547)
                ·
                  refine ⟨36348902091491374343246321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24232601394327582895497547 36348902091491374343246321)
                  ·
                    refine ⟨27261676568618530757434741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36348902091491374343246321 27261676568618530757434741)
                    ·
                      refine ⟨2555782178307987258509507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27261676568618530757434741 2555782178307987258509507)
                      ·
                        rfl

theorem cell23_4977368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 1, 2, 5].length) (baseStart_4977368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4977368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4977368 prefixEnd_4977368 := by exact prefixLift 4977368
  have htrace : WordTrace (prefixWord ++ tailWord_4977368) baseStart_4977368 baseEnd_4977368 := by
    simpa [prefixWord, tailWord_4977368, baseEnd_4977368] using wordTrace_append hprefix tailTrace_4977368
  have hstable : (prefixWord ++ tailWord_4977368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4977368).length < 2 ^ (prefixWord ++ tailWord_4977368).sum := by decide
  have hdescent : baseEnd_4977368 < baseStart_4977368 := by decide
  rcases family_descends (prefixWord ++ tailWord_4977368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4977371 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 3, 10]
def baseStart_4977371 : Nat := 118140960795 + 4977371 * 2 ^ 59
def prefixEnd_4977371 : Nat := 4983230072969 + 3 ^ 40 * 4977371 * 2
def baseEnd_4977371 : Nat := 851927906249983582257331

theorem tailTrace_4977371 : CollatzResearch.WordTrace tailWord_4977371 prefixEnd_4977371 851927906249983582257331 := by
  unfold tailWord_4977371
  simp only [CollatzResearch.WordTrace]
  refine ⟨181539634450842409134595967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121026422967228272756397311 181539634450842409134595967)
  ·
    refine ⟨272309451676263613701893951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181539634450842409134595967 272309451676263613701893951)
    ·
      refine ⟨408464177514395420552840927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272309451676263613701893951 408464177514395420552840927)
      ·
        refine ⟨612696266271593130829261391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 408464177514395420552840927 612696266271593130829261391)
        ·
          refine ⟨919044399407389696243892087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 612696266271593130829261391 919044399407389696243892087)
          ·
            refine ⟨1378566599111084544365838131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 919044399407389696243892087 1378566599111084544365838131)
            ·
              refine ⟨2067849898666626816548757197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1378566599111084544365838131 2067849898666626816548757197)
              ·
                refine ⟨775443711999985056205783949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2067849898666626816548757197 775443711999985056205783949)
                ·
                  refine ⟨290791391999994396077168981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 775443711999985056205783949 290791391999994396077168981)
                  ·
                    refine ⟨851927906249983582257331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 290791391999994396077168981 851927906249983582257331)
                    ·
                      rfl

theorem cell23_4977371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 10].length) (baseStart_4977371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4977371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4977371 prefixEnd_4977371 := by exact prefixLift 4977371
  have htrace : WordTrace (prefixWord ++ tailWord_4977371) baseStart_4977371 baseEnd_4977371 := by
    simpa [prefixWord, tailWord_4977371, baseEnd_4977371] using wordTrace_append hprefix tailTrace_4977371
  have hstable : (prefixWord ++ tailWord_4977371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4977371).length < 2 ^ (prefixWord ++ tailWord_4977371).sum := by decide
  have hdescent : baseEnd_4977371 < baseStart_4977371 := by decide
  rcases family_descends (prefixWord ++ tailWord_4977371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4977379 : List Nat := [1, 1, 1, 7, 1, 3, 2, 2, 5]
def baseStart_4977379 : Nat := 118140960795 + 4977379 * 2 ^ 59
def prefixEnd_4977379 : Nat := 4983230072969 + 3 ^ 40 * 4977379 * 2
def baseEnd_4977379 : Nat := 283976425177242968385773

theorem tailTrace_4977379 : CollatzResearch.WordTrace tailWord_4977379 prefixEnd_4977379 283976425177242968385773 := by
  unfold tailWord_4977379
  simp only [CollatzResearch.WordTrace]
  refine ⟨181539926234813426500887191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 121026617489875617667258127 181539926234813426500887191)
  ·
    refine ⟨272309889352220139751330787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181539926234813426500887191 272309889352220139751330787)
    ·
      refine ⟨408464834028330209626996181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272309889352220139751330787 408464834028330209626996181)
      ·
        refine ⟨9573394547538989288132723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 408464834028330209626996181 9573394547538989288132723)
        ·
          refine ⟨14360091821308483932199085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9573394547538989288132723 14360091821308483932199085)
          ·
            refine ⟨5385034432990681474574657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14360091821308483932199085 5385034432990681474574657)
            ·
              refine ⟨4038775824743011105930993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5385034432990681474574657 4038775824743011105930993)
              ·
                refine ⟨3029081868557258329448245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4038775824743011105930993 3029081868557258329448245)
                ·
                  refine ⟨283976425177242968385773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3029081868557258329448245 283976425177242968385773)
                  ·
                    rfl

theorem cell23_4977379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 2, 2, 5].length) (baseStart_4977379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4977379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4977379 prefixEnd_4977379 := by exact prefixLift 4977379
  have htrace : WordTrace (prefixWord ++ tailWord_4977379) baseStart_4977379 baseEnd_4977379 := by
    simpa [prefixWord, tailWord_4977379, baseEnd_4977379] using wordTrace_append hprefix tailTrace_4977379
  have hstable : (prefixWord ++ tailWord_4977379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4977379).length < 2 ^ (prefixWord ++ tailWord_4977379).sum := by decide
  have hdescent : baseEnd_4977379 < baseStart_4977379 := by decide
  rcases family_descends (prefixWord ++ tailWord_4977379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
