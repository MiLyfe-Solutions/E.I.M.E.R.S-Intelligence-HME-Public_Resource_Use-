import V185TrunkScan23Chunk0738

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4369444 : List Nat := [2, 3, 1, 4, 1, 1, 1, 3, 1, 4, 2]
def baseStart_4369444 : Nat := 118140960795 + 4369444 * 2 ^ 59
def prefixEnd_4369444 : Nat := 4983230072969 + 3 ^ 40 * 4369444 * 2
def baseEnd_4369444 : Nat := 2243624964904107763955299

theorem tailTrace_4369444 : CollatzResearch.WordTrace tailWord_4369444 prefixEnd_4369444 2243624964904107763955299 := by
  unfold tailWord_4369444
  simp only [CollatzResearch.WordTrace]
  refine ⟨79683357591129052234489693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106244476788172069645986257 79683357591129052234489693)
  ·
    refine ⟨29881259096673394587933635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79683357591129052234489693 29881259096673394587933635)
    ·
      refine ⟨44821888645010091881900453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29881259096673394587933635 44821888645010091881900453)
      ·
        refine ⟨8404104120939392227856335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44821888645010091881900453 8404104120939392227856335)
        ·
          refine ⟨12606156181409088341784503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8404104120939392227856335 12606156181409088341784503)
          ·
            refine ⟨18909234272113632512676755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12606156181409088341784503 18909234272113632512676755)
            ·
              refine ⟨28363851408170448769015133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18909234272113632512676755 28363851408170448769015133)
              ·
                refine ⟨10636444278063918288380675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28363851408170448769015133 10636444278063918288380675)
                ·
                  refine ⟨15954666417095877432571013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10636444278063918288380675 15954666417095877432571013)
                  ·
                    refine ⟨2991499953205477018607065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15954666417095877432571013 2991499953205477018607065)
                    ·
                      refine ⟨2243624964904107763955299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2991499953205477018607065 2243624964904107763955299)
                      ·
                        rfl

theorem cell23_4369444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_4369444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4369444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4369444 prefixEnd_4369444 := by exact prefixLift 4369444
  have htrace : WordTrace (prefixWord ++ tailWord_4369444) baseStart_4369444 baseEnd_4369444 := by
    simpa [prefixWord, tailWord_4369444, baseEnd_4369444] using wordTrace_append hprefix tailTrace_4369444
  have hstable : (prefixWord ++ tailWord_4369444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4369444).length < 2 ^ (prefixWord ++ tailWord_4369444).sum := by decide
  have hdescent : baseEnd_4369444 < baseStart_4369444 := by decide
  rcases family_descends (prefixWord ++ tailWord_4369444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4369478 : List Nat := [6, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2]
def baseStart_4369478 : Nat := 118140960795 + 4369478 * 2 ^ 59
def prefixEnd_4369478 : Nat := 4983230072969 + 3 ^ 40 * 4369478 * 2
def baseEnd_4369478 : Nat := 2243642423246360630930143

theorem tailTrace_4369478 : CollatzResearch.WordTrace tailWord_4369478 prefixEnd_4369478 2243642423246360630930143 := by
  unfold tailWord_4369478
  simp only [CollatzResearch.WordTrace]
  refine ⟨4980248602004216508616159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 106245303509423285517144725 4980248602004216508616159)
  ·
    refine ⟨7470372903006324762924239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4980248602004216508616159 7470372903006324762924239)
    ·
      refine ⟨11205559354509487144386359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7470372903006324762924239 11205559354509487144386359)
      ·
        refine ⟨16808339031764230716579539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11205559354509487144386359 16808339031764230716579539)
        ·
          refine ⟨25212508547646346074869309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16808339031764230716579539 25212508547646346074869309)
          ·
            refine ⟨9454690705367379778075991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25212508547646346074869309 9454690705367379778075991)
            ·
              refine ⟨14182036058051069667113987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9454690705367379778075991 14182036058051069667113987)
              ·
                refine ⟨21273054087076604500670981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14182036058051069667113987 21273054087076604500670981)
                ·
                  refine ⟨3988697641326863343875809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21273054087076604500670981 3988697641326863343875809)
                  ·
                    refine ⟨2991523230995147507906857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3988697641326863343875809 2991523230995147507906857)
                    ·
                      refine ⟨2243642423246360630930143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2991523230995147507906857 2243642423246360630930143)
                      ·
                        rfl

theorem cell23_4369478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2].length) (baseStart_4369478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4369478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4369478 prefixEnd_4369478 := by exact prefixLift 4369478
  have htrace : WordTrace (prefixWord ++ tailWord_4369478) baseStart_4369478 baseEnd_4369478 := by
    simpa [prefixWord, tailWord_4369478, baseEnd_4369478] using wordTrace_append hprefix tailTrace_4369478
  have hstable : (prefixWord ++ tailWord_4369478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4369478).length < 2 ^ (prefixWord ++ tailWord_4369478).sum := by decide
  have hdescent : baseEnd_4369478 < baseStart_4369478 := by decide
  rcases family_descends (prefixWord ++ tailWord_4369478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4369480 : List Nat := [2, 1, 3, 1, 1, 1, 4, 1, 4, 5]
def baseStart_4369480 : Nat := 118140960795 + 4369480 * 2 ^ 59
def prefixEnd_4369480 : Nat := 4983230072969 + 3 ^ 40 * 4369480 * 2
def baseEnd_4369480 : Nat := 747881150069223207701711

theorem tailTrace_4369480 : CollatzResearch.WordTrace tailWord_4369480 prefixEnd_4369480 747881150069223207701711 := by
  unfold tailWord_4369480
  simp only [CollatzResearch.WordTrace]
  refine ⟨79684014105063841308644947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106245352140085121744859929 79684014105063841308644947)
  ·
    refine ⟨119526021157595761962967421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79684014105063841308644947 119526021157595761962967421)
    ·
      refine ⟨44822257934098410736112783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119526021157595761962967421 44822257934098410736112783)
      ·
        refine ⟨67233386901147616104169175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44822257934098410736112783 67233386901147616104169175)
        ·
          refine ⟨100850080351721424156253763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67233386901147616104169175 100850080351721424156253763)
          ·
            refine ⟨151275120527582136234380645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100850080351721424156253763 151275120527582136234380645)
            ·
              refine ⟨28364085098921650543946371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 151275120527582136234380645 28364085098921650543946371)
              ·
                refine ⟨42546127648382475815919557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28364085098921650543946371 42546127648382475815919557)
                ·
                  refine ⟨7977398934071714215484917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42546127648382475815919557 7977398934071714215484917)
                  ·
                    refine ⟨747881150069223207701711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7977398934071714215484917 747881150069223207701711)
                    ·
                      rfl

theorem cell23_4369480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 4, 5].length) (baseStart_4369480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4369480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4369480 prefixEnd_4369480 := by exact prefixLift 4369480
  have htrace : WordTrace (prefixWord ++ tailWord_4369480) baseStart_4369480 baseEnd_4369480 := by
    simpa [prefixWord, tailWord_4369480, baseEnd_4369480] using wordTrace_append hprefix tailTrace_4369480
  have hstable : (prefixWord ++ tailWord_4369480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4369480).length < 2 ^ (prefixWord ++ tailWord_4369480).sum := by decide
  have hdescent : baseEnd_4369480 < baseStart_4369480 := by decide
  rcases family_descends (prefixWord ++ tailWord_4369480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4369517 : List Nat := [1, 5, 1, 1, 2, 2, 2, 1, 1, 3, 4]
def baseStart_4369517 : Nat := 118140960795 + 4369517 * 2 ^ 59
def prefixEnd_4369517 : Nat := 4983230072969 + 3 ^ 40 * 4369517 * 2
def baseEnd_4369517 : Nat := 2243662448991885978342463

theorem tailTrace_4369517 : CollatzResearch.WordTrace tailWord_4369517 prefixEnd_4369517 2243662448991885978342463 := by
  unfold tailWord_4369517
  simp only [CollatzResearch.WordTrace]
  refine ⟨159369377710993637936386805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106246251807329091957591203 159369377710993637936386805)
  ·
    refine ⟨14940879160405653556536263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 159369377710993637936386805 14940879160405653556536263)
    ·
      refine ⟨22411318740608480334804395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14940879160405653556536263 22411318740608480334804395)
      ·
        refine ⟨33616978110912720502206593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22411318740608480334804395 33616978110912720502206593)
        ·
          refine ⟨25212733583184540376654945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33616978110912720502206593 25212733583184540376654945)
          ·
            refine ⟨18909550187388405282491209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25212733583184540376654945 18909550187388405282491209)
            ·
              refine ⟨14182162640541303961868407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18909550187388405282491209 14182162640541303961868407)
              ·
                refine ⟨21273243960811955942802611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14182162640541303961868407 21273243960811955942802611)
                ·
                  refine ⟨31909865941217933914203917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21273243960811955942802611 31909865941217933914203917)
                  ·
                    refine ⟨11966199727956725217826469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31909865941217933914203917 11966199727956725217826469)
                    ·
                      refine ⟨2243662448991885978342463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11966199727956725217826469 2243662448991885978342463)
                      ·
                        rfl

theorem cell23_4369517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_4369517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4369517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4369517 prefixEnd_4369517 := by exact prefixLift 4369517
  have htrace : WordTrace (prefixWord ++ tailWord_4369517) baseStart_4369517 baseEnd_4369517 := by
    simpa [prefixWord, tailWord_4369517, baseEnd_4369517] using wordTrace_append hprefix tailTrace_4369517
  have hstable : (prefixWord ++ tailWord_4369517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4369517).length < 2 ^ (prefixWord ++ tailWord_4369517).sum := by decide
  have hdescent : baseEnd_4369517 < baseStart_4369517 := by decide
  rcases family_descends (prefixWord ++ tailWord_4369517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4369580 : List Nat := [2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 5]
def baseStart_4369580 : Nat := 118140960795 + 4369580 * 2 ^ 59
def prefixEnd_4369580 : Nat := 4983230072969 + 3 ^ 40 * 4369580 * 2
def baseEnd_4369580 : Nat := 2243694798273119231854673

theorem tailTrace_4369580 : CollatzResearch.WordTrace tailWord_4369580 prefixEnd_4369580 2243694798273119231854673 := by
  unfold tailWord_4369580
  simp only [CollatzResearch.WordTrace]
  refine ⟨79685837754882699847965097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106247783673176933130620129 79685837754882699847965097)
  ·
    refine ⟨59764378316162024885973823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79685837754882699847965097 59764378316162024885973823)
    ·
      refine ⟨89646567474243037328960735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59764378316162024885973823 89646567474243037328960735)
      ·
        refine ⟨134469851211364555993441103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89646567474243037328960735 134469851211364555993441103)
        ·
          refine ⟨201704776817046833990161655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134469851211364555993441103 201704776817046833990161655)
          ·
            refine ⟨302557165225570250985242483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201704776817046833990161655 302557165225570250985242483)
            ·
              refine ⟨453835747838355376477863725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 302557165225570250985242483 453835747838355376477863725)
              ·
                refine ⟨170188405439383266179198897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 453835747838355376477863725 170188405439383266179198897)
                ·
                  refine ⟨127641304079537449634399173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 170188405439383266179198897 127641304079537449634399173)
                  ·
                    refine ⟨23932744514913271806449845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 127641304079537449634399173 23932744514913271806449845)
                    ·
                      refine ⟨2243694798273119231854673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23932744514913271806449845 2243694798273119231854673)
                      ·
                        rfl

theorem cell23_4369580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 5].length) (baseStart_4369580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4369580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4369580 prefixEnd_4369580 := by exact prefixLift 4369580
  have htrace : WordTrace (prefixWord ++ tailWord_4369580) baseStart_4369580 baseEnd_4369580 := by
    simpa [prefixWord, tailWord_4369580, baseEnd_4369580] using wordTrace_append hprefix tailTrace_4369580
  have hstable : (prefixWord ++ tailWord_4369580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4369580).length < 2 ^ (prefixWord ++ tailWord_4369580).sum := by decide
  have hdescent : baseEnd_4369580 < baseStart_4369580 := by decide
  rcases family_descends (prefixWord ++ tailWord_4369580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4369587 : List Nat := [1, 1, 1, 2, 3, 2, 2, 5, 1, 5]
def baseStart_4369587 : Nat := 118140960795 + 4369587 * 2 ^ 59
def prefixEnd_4369587 : Nat := 4983230072969 + 3 ^ 40 * 4369587 * 2
def baseEnd_4369587 : Nat := 747899464212566901489047

theorem tailTrace_4369587 : CollatzResearch.WordTrace tailWord_4369587 prefixEnd_4369587 747899464212566901489047 := by
  unfold tailWord_4369587
  simp only [CollatzResearch.WordTrace]
  refine ⟨159371930820740039891435015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106247953880493359927623343 159371930820740039891435015)
  ·
    refine ⟨239057896231110059837152523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159371930820740039891435015 239057896231110059837152523)
    ·
      refine ⟨358586844346665089755728785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239057896231110059837152523 358586844346665089755728785)
      ·
        refine ⟨268940133259998817316796589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 358586844346665089755728785 268940133259998817316796589)
        ·
          refine ⟨100852549972499556493798721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 268940133259998817316796589 100852549972499556493798721)
          ·
            refine ⟨75639412479374667370349041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100852549972499556493798721 75639412479374667370349041)
            ·
              refine ⟨56729559359531000527761781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75639412479374667370349041 56729559359531000527761781)
              ·
                refine ⟨5318396189956031299477667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56729559359531000527761781 5318396189956031299477667)
                ·
                  refine ⟨7977594284934046949216501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5318396189956031299477667 7977594284934046949216501)
                  ·
                    refine ⟨747899464212566901489047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7977594284934046949216501 747899464212566901489047)
                    ·
                      rfl

theorem cell23_4369587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 5, 1, 5].length) (baseStart_4369587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4369587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4369587 prefixEnd_4369587 := by exact prefixLift 4369587
  have htrace : WordTrace (prefixWord ++ tailWord_4369587) baseStart_4369587 baseEnd_4369587 := by
    simpa [prefixWord, tailWord_4369587, baseEnd_4369587] using wordTrace_append hprefix tailTrace_4369587
  have hstable : (prefixWord ++ tailWord_4369587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4369587).length < 2 ^ (prefixWord ++ tailWord_4369587).sum := by decide
  have hdescent : baseEnd_4369587 < baseStart_4369587 := by decide
  rcases family_descends (prefixWord ++ tailWord_4369587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4369617 : List Nat := [1, 2, 2, 1, 2, 2, 1, 2, 6, 4]
def baseStart_4369617 : Nat := 118140960795 + 4369617 * 2 ^ 59
def prefixEnd_4369617 : Nat := 4983230072969 + 3 ^ 40 * 4369617 * 2
def baseEnd_4369617 : Nat := 747904599019111862364001

theorem tailTrace_4369617 : CollatzResearch.WordTrace tailWord_4369617 prefixEnd_4369617 747904599019111862364001 := by
  unfold tailWord_4369617
  simp only [CollatzResearch.WordTrace]
  refine ⟨159373025010631355015027105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106248683340420903343351403 159373025010631355015027105)
  ·
    refine ⟨119529768757973516261270329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159373025010631355015027105 119529768757973516261270329)
    ·
      refine ⟨89647326568480137195952747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119529768757973516261270329 89647326568480137195952747)
      ·
        refine ⟨134470989852720205793929121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89647326568480137195952747 134470989852720205793929121)
        ·
          refine ⟨100853242389540154345446841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134470989852720205793929121 100853242389540154345446841)
          ·
            refine ⟨75639931792155115759085131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100853242389540154345446841 75639931792155115759085131)
            ·
              refine ⟨113459897688232673638627697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75639931792155115759085131 113459897688232673638627697)
              ·
                refine ⟨85094923266174505228970773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113459897688232673638627697 85094923266174505228970773)
                ·
                  refine ⟨3988824528101929932608005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 85094923266174505228970773 3988824528101929932608005)
                  ·
                    refine ⟨747904599019111862364001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3988824528101929932608005 747904599019111862364001)
                    ·
                      rfl

theorem cell23_4369617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 6, 4].length) (baseStart_4369617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4369617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4369617 prefixEnd_4369617 := by exact prefixLift 4369617
  have htrace : WordTrace (prefixWord ++ tailWord_4369617) baseStart_4369617 baseEnd_4369617 := by
    simpa [prefixWord, tailWord_4369617, baseEnd_4369617] using wordTrace_append hprefix tailTrace_4369617
  have hstable : (prefixWord ++ tailWord_4369617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4369617).length < 2 ^ (prefixWord ++ tailWord_4369617).sum := by decide
  have hdescent : baseEnd_4369617 < baseStart_4369617 := by decide
  rcases family_descends (prefixWord ++ tailWord_4369617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4369627 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 7, 2, 3]
def baseStart_4369627 : Nat := 118140960795 + 4369627 * 2 ^ 59
def prefixEnd_4369627 : Nat := 4983230072969 + 3 ^ 40 * 4369627 * 2
def baseEnd_4369627 : Nat := 2243718931863880547966957

theorem tailTrace_4369627 : CollatzResearch.WordTrace tailWord_4369627 prefixEnd_4369627 2243718931863880547966957 := by
  unfold tailWord_4369627
  simp only [CollatzResearch.WordTrace]
  refine ⟨159373389740595126722891135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106248926493730084481927423 159373389740595126722891135)
  ·
    refine ⟨239060084610892690084336703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159373389740595126722891135 239060084610892690084336703)
    ·
      refine ⟨358590126916339035126505055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239060084610892690084336703 358590126916339035126505055)
      ·
        refine ⟨537885190374508552689757583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 358590126916339035126505055 537885190374508552689757583)
        ·
          refine ⟨806827785561762829034636375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 537885190374508552689757583 806827785561762829034636375)
          ·
            refine ⟨1210241678342644243551954563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 806827785561762829034636375 1210241678342644243551954563)
            ·
              refine ⟨1815362517513966365327931845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1210241678342644243551954563 1815362517513966365327931845)
              ·
                refine ⟨340380472033868693498987221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1815362517513966365327931845 340380472033868693498987221)
                ·
                  refine ⟨7977667313293797503882513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 340380472033868693498987221 7977667313293797503882513)
                  ·
                    refine ⟨5983250484970348127911885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7977667313293797503882513 5983250484970348127911885)
                    ·
                      refine ⟨2243718931863880547966957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5983250484970348127911885 2243718931863880547966957)
                      ·
                        rfl

theorem cell23_4369627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 7, 2, 3].length) (baseStart_4369627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4369627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4369627 prefixEnd_4369627 := by exact prefixLift 4369627
  have htrace : WordTrace (prefixWord ++ tailWord_4369627) baseStart_4369627 baseEnd_4369627 := by
    simpa [prefixWord, tailWord_4369627, baseEnd_4369627] using wordTrace_append hprefix tailTrace_4369627
  have hstable : (prefixWord ++ tailWord_4369627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4369627).length < 2 ^ (prefixWord ++ tailWord_4369627).sum := by decide
  have hdescent : baseEnd_4369627 < baseStart_4369627 := by decide
  rcases family_descends (prefixWord ++ tailWord_4369627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4369647 : List Nat := [1, 1, 2, 1, 7, 1, 10]
def baseStart_4369647 : Nat := 118140960795 + 4369647 * 2 ^ 59
def prefixEnd_4369647 : Nat := 4983230072969 + 3 ^ 40 * 4369647 * 2
def baseEnd_4369647 : Nat := 27700360512061363823665

theorem tailTrace_4369647 : CollatzResearch.WordTrace tailWord_4369647 prefixEnd_4369647 27700360512061363823665 := by
  unfold tailWord_4369647
  simp only [CollatzResearch.WordTrace]
  refine ⟨159374119200522670138619195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106249412800348446759079463 159374119200522670138619195)
  ·
    refine ⟨239061178800784005207928793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159374119200522670138619195 239061178800784005207928793)
    ·
      refine ⟨179295884100588003905946595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 239061178800784005207928793 179295884100588003905946595)
      ·
        refine ⟨268943826150882005858919893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179295884100588003905946595 268943826150882005858919893)
        ·
          refine ⟨6303370925411297012318435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 268943826150882005858919893 6303370925411297012318435)
          ·
            refine ⟨9455056388116945518477653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6303370925411297012318435 9455056388116945518477653)
            ·
              refine ⟨27700360512061363823665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9455056388116945518477653 27700360512061363823665)
              ·
                rfl

theorem cell23_4369647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 10].length) (baseStart_4369647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4369647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4369647 prefixEnd_4369647 := by exact prefixLift 4369647
  have htrace : WordTrace (prefixWord ++ tailWord_4369647) baseStart_4369647 baseEnd_4369647 := by
    simpa [prefixWord, tailWord_4369647, baseEnd_4369647] using wordTrace_append hprefix tailTrace_4369647
  have hstable : (prefixWord ++ tailWord_4369647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4369647).length < 2 ^ (prefixWord ++ tailWord_4369647).sum := by decide
  have hdescent : baseEnd_4369647 < baseStart_4369647 := by decide
  rcases family_descends (prefixWord ++ tailWord_4369647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4369651 : List Nat := [1, 1, 1, 2, 2, 7, 1, 2, 2, 4]
def baseStart_4369651 : Nat := 118140960795 + 4369651 * 2 ^ 59
def prefixEnd_4369651 : Nat := 4983230072969 + 3 ^ 40 * 4369651 * 2
def baseEnd_4369651 : Nat := 747910418466529484688949

theorem tailTrace_4369651 : CollatzResearch.WordTrace tailWord_4369651 prefixEnd_4369651 747910418466529484688949 := by
  unfold tailWord_4369651
  simp only [CollatzResearch.WordTrace]
  refine ⟨159374265092508178821764807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106249510061672119214509871 159374265092508178821764807)
  ·
    refine ⟨239061397638762268232647211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159374265092508178821764807 239061397638762268232647211)
    ·
      refine ⟨358592096458143402348970817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239061397638762268232647211 358592096458143402348970817)
      ·
        refine ⟨268944072343607551761728113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 358592096458143402348970817 268944072343607551761728113)
        ·
          refine ⟨201708054257705663821296085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 268944072343607551761728113 201708054257705663821296085)
          ·
            refine ⟨4727532521664976495811627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 201708054257705663821296085 4727532521664976495811627)
            ·
              refine ⟨7091298782497464743717441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4727532521664976495811627 7091298782497464743717441)
              ·
                refine ⟨5318474086873098557788081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7091298782497464743717441 5318474086873098557788081)
                ·
                  refine ⟨3988855565154823918341061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5318474086873098557788081 3988855565154823918341061)
                  ·
                    refine ⟨747910418466529484688949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3988855565154823918341061 747910418466529484688949)
                    ·
                      rfl

theorem cell23_4369651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 2, 2, 4].length) (baseStart_4369651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4369651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4369651 prefixEnd_4369651 := by exact prefixLift 4369651
  have htrace : WordTrace (prefixWord ++ tailWord_4369651) baseStart_4369651 baseEnd_4369651 := by
    simpa [prefixWord, tailWord_4369651, baseEnd_4369651] using wordTrace_append hprefix tailTrace_4369651
  have hstable : (prefixWord ++ tailWord_4369651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4369651).length < 2 ^ (prefixWord ++ tailWord_4369651).sum := by decide
  have hdescent : baseEnd_4369651 < baseStart_4369651 := by decide
  rcases family_descends (prefixWord ++ tailWord_4369651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4369652 : List Nat := [2, 6, 1, 2, 1, 1, 2, 1, 3, 1, 3]
def baseStart_4369652 : Nat := 118140960795 + 4369652 * 2 ^ 59
def prefixEnd_4369652 : Nat := 4983230072969 + 3 ^ 40 * 4369652 * 2
def baseEnd_4369652 : Nat := 2243731768880242950154343

theorem tailTrace_4369652 : CollatzResearch.WordTrace tailWord_4369652 prefixEnd_4369652 2243731768880242950154343 := by
  unfold tailWord_4369652
  simp only [CollatzResearch.WordTrace]
  refine ⟨79687150782752277996275605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106249534377003037328367473 79687150782752277996275605)
  ·
    refine ⟨3735335192941513031075419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 79687150782752277996275605 3735335192941513031075419)
    ·
      refine ⟨5603002789412269546613129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3735335192941513031075419 5603002789412269546613129)
      ·
        refine ⟨4202252092059202159959847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5603002789412269546613129 4202252092059202159959847)
        ·
          refine ⟨6303378138088803239939771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4202252092059202159959847 6303378138088803239939771)
          ·
            refine ⟨9455067207133204859909657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6303378138088803239939771 9455067207133204859909657)
            ·
              refine ⟨7091300405349903644932243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9455067207133204859909657 7091300405349903644932243)
              ·
                refine ⟨10636950608024855467398365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7091300405349903644932243 10636950608024855467398365)
                ·
                  refine ⟨3988856478009320800274387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10636950608024855467398365 3988856478009320800274387)
                  ·
                    refine ⟨5983284717013981200411581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3988856478009320800274387 5983284717013981200411581)
                    ·
                      refine ⟨2243731768880242950154343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5983284717013981200411581 2243731768880242950154343)
                      ·
                        rfl

theorem cell23_4369652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_4369652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4369652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4369652 prefixEnd_4369652 := by exact prefixLift 4369652
  have htrace : WordTrace (prefixWord ++ tailWord_4369652) baseStart_4369652 baseEnd_4369652 := by
    simpa [prefixWord, tailWord_4369652, baseEnd_4369652] using wordTrace_append hprefix tailTrace_4369652
  have hstable : (prefixWord ++ tailWord_4369652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4369652).length < 2 ^ (prefixWord ++ tailWord_4369652).sum := by decide
  have hdescent : baseEnd_4369652 < baseStart_4369652 := by decide
  rcases family_descends (prefixWord ++ tailWord_4369652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4369658 : List Nat := [3, 1, 1, 1, 1, 4, 1, 6, 1, 2, 2]
def baseStart_4369658 : Nat := 118140960795 + 4369658 * 2 ^ 59
def prefixEnd_4369658 : Nat := 4983230072969 + 3 ^ 40 * 4369658 * 2
def baseEnd_4369658 : Nat := 2243734849764169926679315

theorem tailTrace_4369658 : CollatzResearch.WordTrace tailWord_4369658 prefixEnd_4369658 2243734849764169926679315 := by
  unfold tailWord_4369658
  simp only [CollatzResearch.WordTrace]
  refine ⟨39843630100870704754317407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106249680268988546011513085 39843630100870704754317407)
  ·
    refine ⟨59765445151306057131476111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39843630100870704754317407 59765445151306057131476111)
    ·
      refine ⟨89648167726959085697214167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59765445151306057131476111 89648167726959085697214167)
      ·
        refine ⟨134472251590438628545821251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89648167726959085697214167 134472251590438628545821251)
        ·
          refine ⟨201708377385657942818731877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134472251590438628545821251 201708377385657942818731877)
          ·
            refine ⟨37820320759810864278512227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 201708377385657942818731877 37820320759810864278512227)
            ·
              refine ⟨56730481139716296417768341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37820320759810864278512227 56730481139716296417768341)
              ·
                refine ⟨2659241303424201394582891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 56730481139716296417768341 2659241303424201394582891)
                ·
                  refine ⟨3988861955136302091874337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2659241303424201394582891 3988861955136302091874337)
                  ·
                    refine ⟨2991646466352226568905753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3988861955136302091874337 2991646466352226568905753)
                    ·
                      refine ⟨2243734849764169926679315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2991646466352226568905753 2243734849764169926679315)
                      ·
                        rfl

theorem cell23_4369658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 6, 1, 2, 2].length) (baseStart_4369658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4369658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4369658 prefixEnd_4369658 := by exact prefixLift 4369658
  have htrace : WordTrace (prefixWord ++ tailWord_4369658) baseStart_4369658 baseEnd_4369658 := by
    simpa [prefixWord, tailWord_4369658, baseEnd_4369658] using wordTrace_append hprefix tailTrace_4369658
  have hstable : (prefixWord ++ tailWord_4369658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4369658).length < 2 ^ (prefixWord ++ tailWord_4369658).sum := by decide
  have hdescent : baseEnd_4369658 < baseStart_4369658 := by decide
  rcases family_descends (prefixWord ++ tailWord_4369658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4369668 : List Nat := [2, 3, 2, 2, 2, 2, 3, 1, 2, 4]
def baseStart_4369668 : Nat := 118140960795 + 4369668 * 2 ^ 59
def prefixEnd_4369668 : Nat := 4983230072969 + 3 ^ 40 * 4369668 * 2
def baseEnd_4369668 : Nat := 747913328190238295851423

theorem tailTrace_4369668 : CollatzResearch.WordTrace tailWord_4369668 prefixEnd_4369668 747913328190238295851423 := by
  unfold tailWord_4369668
  simp only [CollatzResearch.WordTrace]
  refine ⟨79687442566723295362566829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106249923422297727150089105 79687442566723295362566829)
  ·
    refine ⟨29882790962521235760962561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79687442566723295362566829 29882790962521235760962561)
    ·
      refine ⟨22412093221890926820721921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29882790962521235760962561 22412093221890926820721921)
      ·
        refine ⟨16809069916418195115541441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22412093221890926820721921 16809069916418195115541441)
        ·
          refine ⟨12606802437313646336656081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16809069916418195115541441 12606802437313646336656081)
          ·
            refine ⟨9455101827985234752492061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12606802437313646336656081 9455101827985234752492061)
            ·
              refine ⟨3545663185494463032184523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9455101827985234752492061 3545663185494463032184523)
              ·
                refine ⟨5318494778241694548276785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3545663185494463032184523 5318494778241694548276785)
                ·
                  refine ⟨3988871083681270911207589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5318494778241694548276785 3988871083681270911207589)
                  ·
                    refine ⟨747913328190238295851423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3988871083681270911207589 747913328190238295851423)
                    ·
                      rfl

theorem cell23_4369668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 3, 1, 2, 4].length) (baseStart_4369668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4369668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4369668 prefixEnd_4369668 := by exact prefixLift 4369668
  have htrace : WordTrace (prefixWord ++ tailWord_4369668) baseStart_4369668 baseEnd_4369668 := by
    simpa [prefixWord, tailWord_4369668, baseEnd_4369668] using wordTrace_append hprefix tailTrace_4369668
  have hstable : (prefixWord ++ tailWord_4369668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4369668).length < 2 ^ (prefixWord ++ tailWord_4369668).sum := by decide
  have hdescent : baseEnd_4369668 < baseStart_4369668 := by decide
  rcases family_descends (prefixWord ++ tailWord_4369668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4369687 : List Nat := [1, 1, 3, 4, 1, 1, 1, 1, 1, 4, 5]
def baseStart_4369687 : Nat := 118140960795 + 4369687 * 2 ^ 59
def prefixEnd_4369687 : Nat := 4983230072969 + 3 ^ 40 * 4369687 * 2
def baseEnd_4369687 : Nat := 2243749740703150313216681

theorem tailTrace_4369687 : CollatzResearch.WordTrace tailWord_4369687 prefixEnd_4369687 2243749740703150313216681 := by
  unfold tailWord_4369687
  simp only [CollatzResearch.WordTrace]
  refine ⟨159375578120377756970075315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106250385413585171313383543 159375578120377756970075315)
  ·
    refine ⟨239063367180566635455112973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159375578120377756970075315 239063367180566635455112973)
    ·
      refine ⟨89648762692712488295667365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 239063367180566635455112973 89648762692712488295667365)
      ·
        refine ⟨16809143004883591555437631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 89648762692712488295667365 16809143004883591555437631)
        ·
          refine ⟨25213714507325387333156447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16809143004883591555437631 25213714507325387333156447)
          ·
            refine ⟨37820571760988080999734671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25213714507325387333156447 37820571760988080999734671)
            ·
              refine ⟨56730857641482121499602007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37820571760988080999734671 56730857641482121499602007)
              ·
                refine ⟨85096286462223182249403011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56730857641482121499602007 85096286462223182249403011)
                ·
                  refine ⟨127644429693334773374104517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85096286462223182249403011 127644429693334773374104517)
                  ·
                    refine ⟨23933330567500270007644597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 127644429693334773374104517 23933330567500270007644597)
                    ·
                      refine ⟨2243749740703150313216681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23933330567500270007644597 2243749740703150313216681)
                      ·
                        rfl

theorem cell23_4369687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_4369687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4369687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4369687 prefixEnd_4369687 := by exact prefixLift 4369687
  have htrace : WordTrace (prefixWord ++ tailWord_4369687) baseStart_4369687 baseEnd_4369687 := by
    simpa [prefixWord, tailWord_4369687, baseEnd_4369687] using wordTrace_append hprefix tailTrace_4369687
  have hstable : (prefixWord ++ tailWord_4369687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4369687).length < 2 ^ (prefixWord ++ tailWord_4369687).sum := by decide
  have hdescent : baseEnd_4369687 < baseStart_4369687 := by decide
  rcases family_descends (prefixWord ++ tailWord_4369687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4369697 : List Nat := [1, 2, 3, 2, 1, 1, 1, 2, 1, 5, 4]
def baseStart_4369697 : Nat := 118140960795 + 4369697 * 2 ^ 59
def prefixEnd_4369697 : Nat := 4983230072969 + 3 ^ 40 * 4369697 * 2
def baseEnd_4369697 : Nat := 2243754875509695274091635

theorem tailTrace_4369697 : CollatzResearch.WordTrace tailWord_4369697 prefixEnd_4369697 2243754875509695274091635 := by
  unfold tailWord_4369697
  simp only [CollatzResearch.WordTrace]
  refine ⟨159375942850341528677939345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106250628566894352451959563 159375942850341528677939345)
  ·
    refine ⟨119531957137756146508454509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159375942850341528677939345 119531957137756146508454509)
    ·
      refine ⟨44824483926658554940670441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119531957137756146508454509 44824483926658554940670441)
      ·
        refine ⟨33618362944993916205502831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44824483926658554940670441 33618362944993916205502831)
        ·
          refine ⟨50427544417490874308254247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33618362944993916205502831 50427544417490874308254247)
          ·
            refine ⟨75641316626236311462381371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50427544417490874308254247 75641316626236311462381371)
            ·
              refine ⟨113461974939354467193572057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75641316626236311462381371 113461974939354467193572057)
              ·
                refine ⟨85096481204515850395179043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113461974939354467193572057 85096481204515850395179043)
                ·
                  refine ⟨127644721806773775592768565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85096481204515850395179043 127644721806773775592768565)
                  ·
                    refine ⟨11966692669385041461822053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 127644721806773775592768565 11966692669385041461822053)
                    ·
                      refine ⟨2243754875509695274091635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11966692669385041461822053 2243754875509695274091635)
                      ·
                        rfl

theorem cell23_4369697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_4369697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4369697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4369697 prefixEnd_4369697 := by exact prefixLift 4369697
  have htrace : WordTrace (prefixWord ++ tailWord_4369697) baseStart_4369697 baseEnd_4369697 := by
    simpa [prefixWord, tailWord_4369697, baseEnd_4369697] using wordTrace_append hprefix tailTrace_4369697
  have hstable : (prefixWord ++ tailWord_4369697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4369697).length < 2 ^ (prefixWord ++ tailWord_4369697).sum := by decide
  have hdescent : baseEnd_4369697 < baseStart_4369697 := by decide
  rcases family_descends (prefixWord ++ tailWord_4369697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4369709 : List Nat := [1, 5, 3, 1, 1, 2, 3, 2, 1, 2, 2]
def baseStart_4369709 : Nat := 118140960795 + 4369709 * 2 ^ 59
def prefixEnd_4369709 : Nat := 4983230072969 + 3 ^ 40 * 4369709 * 2
def baseEnd_4369709 : Nat := 2243761037277549227141581

theorem tailTrace_4369709 : CollatzResearch.WordTrace tailWord_4369709 prefixEnd_4369709 2243761037277549227141581 := by
  unfold tailWord_4369709
  simp only [CollatzResearch.WordTrace]
  refine ⟨159376380526298054727376181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106250920350865369818250787 159376380526298054727376181)
  ·
    refine ⟨14941535674340442630691517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 159376380526298054727376181 14941535674340442630691517)
    ·
      refine ⟨5603075877877665986509319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14941535674340442630691517 5603075877877665986509319)
      ·
        refine ⟨8404613816816498979763979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5603075877877665986509319 8404613816816498979763979)
        ·
          refine ⟨12606920725224748469645969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8404613816816498979763979 12606920725224748469645969)
          ·
            refine ⟨9455190543918561352234477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12606920725224748469645969 9455190543918561352234477)
            ·
              refine ⟨3545696453969460507087929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9455190543918561352234477 3545696453969460507087929)
              ·
                refine ⟨2659272340477095380315947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3545696453969460507087929 2659272340477095380315947)
                ·
                  refine ⟨3988908510715643070473921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2659272340477095380315947 3988908510715643070473921)
                  ·
                    refine ⟨2991681383036732302855441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3988908510715643070473921 2991681383036732302855441)
                    ·
                      refine ⟨2243761037277549227141581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2991681383036732302855441 2243761037277549227141581)
                      ·
                        rfl

theorem cell23_4369709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_4369709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4369709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4369709 prefixEnd_4369709 := by exact prefixLift 4369709
  have htrace : WordTrace (prefixWord ++ tailWord_4369709) baseStart_4369709 baseEnd_4369709 := by
    simpa [prefixWord, tailWord_4369709, baseEnd_4369709] using wordTrace_append hprefix tailTrace_4369709
  have hstable : (prefixWord ++ tailWord_4369709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4369709).length < 2 ^ (prefixWord ++ tailWord_4369709).sum := by decide
  have hdescent : baseEnd_4369709 < baseStart_4369709 := by decide
  rcases family_descends (prefixWord ++ tailWord_4369709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4369725 : List Nat := [1, 4, 1, 5, 1, 1, 1, 3, 2, 1, 3]
def baseStart_4369725 : Nat := 118140960795 + 4369725 * 2 ^ 59
def prefixEnd_4369725 : Nat := 4983230072969 + 3 ^ 40 * 4369725 * 2
def baseEnd_4369725 : Nat := 2243769252968021164541507

theorem tailTrace_4369725 : CollatzResearch.WordTrace tailWord_4369725 prefixEnd_4369725 2243769252968021164541507 := by
  unfold tailWord_4369725
  simp only [CollatzResearch.WordTrace]
  refine ⟨159376964094240089459958629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106251309396160059639972419 159376964094240089459958629)
  ·
    refine ⟨29883180767670016773742243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 159376964094240089459958629 29883180767670016773742243)
    ·
      refine ⟨44824771151505025160613365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29883180767670016773742243 44824771151505025160613365)
      ·
        refine ⟨4202322295453596108807503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44824771151505025160613365 4202322295453596108807503)
        ·
          refine ⟨6303483443180394163211255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4202322295453596108807503 6303483443180394163211255)
          ·
            refine ⟨9455225164770591244816883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6303483443180394163211255 9455225164770591244816883)
            ·
              refine ⟨14182837747155886867225325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9455225164770591244816883 14182837747155886867225325)
              ·
                refine ⟨5318564155183457575209497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14182837747155886867225325 5318564155183457575209497)
                ·
                  refine ⟨3988923116387593181407123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5318564155183457575209497 3988923116387593181407123)
                  ·
                    refine ⟨5983384674581389772110685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3988923116387593181407123 5983384674581389772110685)
                    ·
                      refine ⟨2243769252968021164541507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5983384674581389772110685 2243769252968021164541507)
                      ·
                        rfl

theorem cell23_4369725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_4369725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4369725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4369725 prefixEnd_4369725 := by exact prefixLift 4369725
  have htrace : WordTrace (prefixWord ++ tailWord_4369725) baseStart_4369725 baseEnd_4369725 := by
    simpa [prefixWord, tailWord_4369725, baseEnd_4369725] using wordTrace_append hprefix tailTrace_4369725
  have hstable : (prefixWord ++ tailWord_4369725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4369725).length < 2 ^ (prefixWord ++ tailWord_4369725).sum := by decide
  have hdescent : baseEnd_4369725 < baseStart_4369725 := by decide
  rcases family_descends (prefixWord ++ tailWord_4369725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4369737 : List Nat := [1, 2, 1, 1, 2, 3, 2, 4, 7]
def baseStart_4369737 : Nat := 118140960795 + 4369737 * 2 ^ 59
def prefixEnd_4369737 : Nat := 4983230072969 + 3 ^ 40 * 4369737 * 2
def baseEnd_4369737 : Nat := 249308379415097235287939

theorem tailTrace_4369737 : CollatzResearch.WordTrace tailWord_4369737 prefixEnd_4369737 249308379415097235287939 := by
  unfold tailWord_4369737
  simp only [CollatzResearch.WordTrace]
  refine ⟨159377401770196615509395465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106251601180131077006263643 159377401770196615509395465)
  ·
    refine ⟨119533051327647461632046599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159377401770196615509395465 119533051327647461632046599)
    ·
      refine ⟨179299576991471192448069899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119533051327647461632046599 179299576991471192448069899)
      ·
        refine ⟨268949365487206788672104849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179299576991471192448069899 268949365487206788672104849)
        ·
          refine ⟨201712024115405091504078637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 268949365487206788672104849 201712024115405091504078637)
          ·
            refine ⟨75642009043276909314029489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 201712024115405091504078637 75642009043276909314029489)
            ·
              refine ⟨56731506782457681985522117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75642009043276909314029489 56731506782457681985522117)
              ·
                refine ⟨10637157521710815372285397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56731506782457681985522117 10637157521710815372285397)
                ·
                  refine ⟨249308379415097235287939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10637157521710815372285397 249308379415097235287939)
                  ·
                    rfl

theorem cell23_4369737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 4, 7].length) (baseStart_4369737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4369737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4369737 prefixEnd_4369737 := by exact prefixLift 4369737
  have htrace : WordTrace (prefixWord ++ tailWord_4369737) baseStart_4369737 baseEnd_4369737 := by
    simpa [prefixWord, tailWord_4369737, baseEnd_4369737] using wordTrace_append hprefix tailTrace_4369737
  have hstable : (prefixWord ++ tailWord_4369737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4369737).length < 2 ^ (prefixWord ++ tailWord_4369737).sum := by decide
  have hdescent : baseEnd_4369737 < baseStart_4369737 := by decide
  rcases family_descends (prefixWord ++ tailWord_4369737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4369804 : List Nat := [2, 2, 1, 2, 1, 3, 3, 1, 1, 3, 4]
def baseStart_4369804 : Nat := 118140960795 + 4369804 * 2 ^ 59
def prefixEnd_4369804 : Nat := 4983230072969 + 3 ^ 40 * 4369804 * 2
def baseEnd_4369804 : Nat := 2243809817939726355453643

theorem tailTrace_4369804 : CollatzResearch.WordTrace tailWord_4369804 prefixEnd_4369804 2243809817939726355453643 := by
  unfold tailWord_4369804
  simp only [CollatzResearch.WordTrace]
  refine ⟨79689922730476942976042233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106253230307302590634722977 79689922730476942976042233)
  ·
    refine ⟨59767442047857707232031675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79689922730476942976042233 59767442047857707232031675)
    ·
      refine ⟨89651163071786560848047513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59767442047857707232031675 89651163071786560848047513)
      ·
        refine ⟨67238372303839920636035635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89651163071786560848047513 67238372303839920636035635)
        ·
          refine ⟨100857558455759880954053453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67238372303839920636035635 100857558455759880954053453)
          ·
            refine ⟨37821584420909955357770045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100857558455759880954053453 37821584420909955357770045)
            ·
              refine ⟨14183094157841233259163767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37821584420909955357770045 14183094157841233259163767)
              ·
                refine ⟨21274641236761849888745651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14183094157841233259163767 21274641236761849888745651)
                ·
                  refine ⟨31911961855142774833118477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21274641236761849888745651 31911961855142774833118477)
                  ·
                    refine ⟨11966985695678540562419429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31911961855142774833118477 11966985695678540562419429)
                    ·
                      refine ⟨2243809817939726355453643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11966985695678540562419429 2243809817939726355453643)
                      ·
                        rfl

theorem cell23_4369804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 1, 3, 4].length) (baseStart_4369804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4369804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4369804 prefixEnd_4369804 := by exact prefixLift 4369804
  have htrace : WordTrace (prefixWord ++ tailWord_4369804) baseStart_4369804 baseEnd_4369804 := by
    simpa [prefixWord, tailWord_4369804, baseEnd_4369804] using wordTrace_append hprefix tailTrace_4369804
  have hstable : (prefixWord ++ tailWord_4369804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4369804).length < 2 ^ (prefixWord ++ tailWord_4369804).sum := by decide
  have hdescent : baseEnd_4369804 < baseStart_4369804 := by decide
  rcases family_descends (prefixWord ++ tailWord_4369804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4369871 : List Nat := [1, 1, 2, 1, 1, 4, 2, 2, 5, 1, 3]
def baseStart_4369871 : Nat := 118140960795 + 4369871 * 2 ^ 59
def prefixEnd_4369871 : Nat := 4983230072969 + 3 ^ 40 * 4369871 * 2
def baseEnd_4369871 : Nat := 2243844221143577593315835

theorem tailTrace_4369871 : CollatzResearch.WordTrace tailWord_4369871 prefixEnd_4369871 2243844221143577593315835 := by
  unfold tailWord_4369871
  simp only [CollatzResearch.WordTrace]
  refine ⟨159382289151711156394773467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106254859434474104263182311 159382289151711156394773467)
  ·
    refine ⟨239073433727566734592160201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159382289151711156394773467 239073433727566734592160201)
    ·
      refine ⟨179305075295675050944120151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 239073433727566734592160201 179305075295675050944120151)
      ·
        refine ⟨268957612943512576416180227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179305075295675050944120151 268957612943512576416180227)
        ·
          refine ⟨403436419415268864624270341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268957612943512576416180227 403436419415268864624270341)
          ·
            refine ⟨75644328640362912117050689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 403436419415268864624270341 75644328640362912117050689)
            ·
              refine ⟨56733246480272184087788017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75644328640362912117050689 56733246480272184087788017)
              ·
                refine ⟨42549934860204138065841013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56733246480272184087788017 42549934860204138065841013)
                ·
                  refine ⟨3989056393144137943672595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42549934860204138065841013 3989056393144137943672595)
                  ·
                    refine ⟨5983584589716206915508893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3989056393144137943672595 5983584589716206915508893)
                    ·
                      refine ⟨2243844221143577593315835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5983584589716206915508893 2243844221143577593315835)
                      ·
                        rfl

theorem cell23_4369871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 5, 1, 3].length) (baseStart_4369871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4369871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4369871 prefixEnd_4369871 := by exact prefixLift 4369871
  have htrace : WordTrace (prefixWord ++ tailWord_4369871) baseStart_4369871 baseEnd_4369871 := by
    simpa [prefixWord, tailWord_4369871, baseEnd_4369871] using wordTrace_append hprefix tailTrace_4369871
  have hstable : (prefixWord ++ tailWord_4369871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4369871).length < 2 ^ (prefixWord ++ tailWord_4369871).sum := by decide
  have hdescent : baseEnd_4369871 < baseStart_4369871 := by decide
  rcases family_descends (prefixWord ++ tailWord_4369871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4369911 : List Nat := [1, 1, 3, 1, 1, 1, 1, 8, 1, 1, 4]
def baseStart_4369911 : Nat := 118140960795 + 4369911 * 2 ^ 59
def prefixEnd_4369911 : Nat := 4983230072969 + 3 ^ 40 * 4369911 * 2
def baseEnd_4369911 : Nat := 2243864760369757436815651

theorem tailTrace_4369911 : CollatzResearch.WordTrace tailWord_4369911 prefixEnd_4369911 2243864760369757436815651 := by
  unfold tailWord_4369911
  simp only [CollatzResearch.WordTrace]
  refine ⟨159383748071566243226229587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106255832047710828817486391 159383748071566243226229587)
  ·
    refine ⟨239075622107349364839344381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159383748071566243226229587 239075622107349364839344381)
    ·
      refine ⟨89653358290256011814754143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 239075622107349364839344381 89653358290256011814754143)
      ·
        refine ⟨134480037435384017722131215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89653358290256011814754143 134480037435384017722131215)
        ·
          refine ⟨201720056153076026583196823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134480037435384017722131215 201720056153076026583196823)
          ·
            refine ⟨302580084229614039874795235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201720056153076026583196823 302580084229614039874795235)
            ·
              refine ⟨453870126344421059812192853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 302580084229614039874795235 453870126344421059812192853)
              ·
                refine ⟨5318790543098684294674135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 453870126344421059812192853 5318790543098684294674135)
                ·
                  refine ⟨7978185814648026442011203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5318790543098684294674135 7978185814648026442011203)
                  ·
                    refine ⟨11967278721972039663016805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7978185814648026442011203 11967278721972039663016805)
                    ·
                      refine ⟨2243864760369757436815651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11967278721972039663016805 2243864760369757436815651)
                      ·
                        rfl

theorem cell23_4369911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 8, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 8, 1, 1, 4].length) (baseStart_4369911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4369911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4369911 prefixEnd_4369911 := by exact prefixLift 4369911
  have htrace : WordTrace (prefixWord ++ tailWord_4369911) baseStart_4369911 baseEnd_4369911 := by
    simpa [prefixWord, tailWord_4369911, baseEnd_4369911] using wordTrace_append hprefix tailTrace_4369911
  have hstable : (prefixWord ++ tailWord_4369911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4369911).length < 2 ^ (prefixWord ++ tailWord_4369911).sum := by decide
  have hdescent : baseEnd_4369911 < baseStart_4369911 := by decide
  rcases family_descends (prefixWord ++ tailWord_4369911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4369933 : List Nat := [1, 7, 1, 1, 3, 1, 2, 2, 1, 4]
def baseStart_4369933 : Nat := 118140960795 + 4369933 * 2 ^ 59
def prefixEnd_4369933 : Nat := 4983230072969 + 3 ^ 40 * 4369933 * 2
def baseEnd_4369933 : Nat := 747958685648052116913517

theorem tailTrace_4369933 : CollatzResearch.WordTrace tailWord_4369933 prefixEnd_4369933 747958685648052116913517 := by
  unfold tailWord_4369933
  simp only [CollatzResearch.WordTrace]
  refine ⟨159384550477486540983530453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106256366984991027322353635 159384550477486540983530453)
  ·
    refine ⟨3735575401816090804301495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 159384550477486540983530453 3735575401816090804301495)
    ·
      refine ⟨5603363102724136206452243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3735575401816090804301495 5603363102724136206452243)
      ·
        refine ⟨8405044654086204309678365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5603363102724136206452243 8405044654086204309678365)
        ·
          refine ⟨3151891745282326616129387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8405044654086204309678365 3151891745282326616129387)
          ·
            refine ⟨4727837617923489924194081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3151891745282326616129387 4727837617923489924194081)
            ·
              refine ⟨3545878213442617443145561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4727837617923489924194081 3545878213442617443145561)
              ·
                refine ⟨2659408660081963082359171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3545878213442617443145561 2659408660081963082359171)
                ·
                  refine ⟨3989112990122944623538757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2659408660081963082359171 3989112990122944623538757)
                  ·
                    refine ⟨747958685648052116913517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3989112990122944623538757 747958685648052116913517)
                    ·
                      rfl

theorem cell23_4369933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_4369933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4369933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4369933 prefixEnd_4369933 := by exact prefixLift 4369933
  have htrace : WordTrace (prefixWord ++ tailWord_4369933) baseStart_4369933 baseEnd_4369933 := by
    simpa [prefixWord, tailWord_4369933, baseEnd_4369933] using wordTrace_append hprefix tailTrace_4369933
  have hstable : (prefixWord ++ tailWord_4369933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4369933).length < 2 ^ (prefixWord ++ tailWord_4369933).sum := by decide
  have hdescent : baseEnd_4369933 < baseStart_4369933 := by decide
  rcases family_descends (prefixWord ++ tailWord_4369933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4369934 : List Nat := [4, 1, 1, 2, 15]
def baseStart_4369934 : Nat := 118140960795 + 4369934 * 2 ^ 59
def prefixEnd_4369934 : Nat := 4983230072969 + 3 ^ 40 * 4369934 * 2
def baseEnd_4369934 : Nat := 3078019986865309803605

theorem tailTrace_4369934 : CollatzResearch.WordTrace tailWord_4369934 prefixEnd_4369934 3078019986865309803605 := by
  unfold tailWord_4369934
  simp only [CollatzResearch.WordTrace]
  refine ⟨19923073368810364769289607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106256391300321945436211237 19923073368810364769289607)
  ·
    refine ⟨29884610053215547153934411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19923073368810364769289607 29884610053215547153934411)
    ·
      refine ⟨44826915079823320730901617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29884610053215547153934411 44826915079823320730901617)
      ·
        refine ⟨33620186309867490548176213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44826915079823320730901617 33620186309867490548176213)
        ·
          refine ⟨3078019986865309803605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 33620186309867490548176213 3078019986865309803605)
          ·
            rfl

theorem cell23_4369934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 15].length) (baseStart_4369934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4369934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4369934 prefixEnd_4369934 := by exact prefixLift 4369934
  have htrace : WordTrace (prefixWord ++ tailWord_4369934) baseStart_4369934 baseEnd_4369934 := by
    simpa [prefixWord, tailWord_4369934, baseEnd_4369934] using wordTrace_append hprefix tailTrace_4369934
  have hstable : (prefixWord ++ tailWord_4369934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4369934).length < 2 ^ (prefixWord ++ tailWord_4369934).sum := by decide
  have hdescent : baseEnd_4369934 < baseStart_4369934 := by decide
  rcases family_descends (prefixWord ++ tailWord_4369934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4369978 : List Nat := [3, 1, 1, 1, 3, 2, 2, 2, 4, 1, 3]
def baseStart_4369978 : Nat := 118140960795 + 4369978 * 2 ^ 59
def prefixEnd_4369978 : Nat := 4983230072969 + 3 ^ 40 * 4369978 * 2
def baseEnd_4369978 : Nat := 2243899163573608674677843

theorem tailTrace_4369978 : CollatzResearch.WordTrace tailWord_4369978 prefixEnd_4369978 2243899163573608674677843 := by
  unfold tailWord_4369978
  simp only [CollatzResearch.WordTrace]
  refine ⟨39846547940580878417229647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106257461174882342445945725 39846547940580878417229647)
  ·
    refine ⟨59769821910871317625844471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39846547940580878417229647 59769821910871317625844471)
    ·
      refine ⟨89654732866306976438766707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59769821910871317625844471 89654732866306976438766707)
      ·
        refine ⟨134482099299460464658150061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89654732866306976438766707 134482099299460464658150061)
        ·
          refine ⟨50430787237297674246806273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134482099299460464658150061 50430787237297674246806273)
          ·
            refine ⟨37823090427973255685104705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50430787237297674246806273 37823090427973255685104705)
            ·
              refine ⟨28367317820979941763828529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37823090427973255685104705 28367317820979941763828529)
              ·
                refine ⟨21275488365734956322871397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28367317820979941763828529 21275488365734956322871397)
                ·
                  refine ⟨3989154068575304310538387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21275488365734956322871397 3989154068575304310538387)
                  ·
                    refine ⟨5983731102862956465807581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3989154068575304310538387 5983731102862956465807581)
                    ·
                      refine ⟨2243899163573608674677843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5983731102862956465807581 2243899163573608674677843)
                      ·
                        rfl

theorem cell23_4369978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 4, 1, 3].length) (baseStart_4369978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4369978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4369978 prefixEnd_4369978 := by exact prefixLift 4369978
  have htrace : WordTrace (prefixWord ++ tailWord_4369978) baseStart_4369978 baseEnd_4369978 := by
    simpa [prefixWord, tailWord_4369978, baseEnd_4369978] using wordTrace_append hprefix tailTrace_4369978
  have hstable : (prefixWord ++ tailWord_4369978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4369978).length < 2 ^ (prefixWord ++ tailWord_4369978).sum := by decide
  have hdescent : baseEnd_4369978 < baseStart_4369978 := by decide
  rcases family_descends (prefixWord ++ tailWord_4369978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4370006 : List Nat := [5, 2, 2, 2, 1, 1, 3, 1, 2, 4]
def baseStart_4370006 : Nat := 118140960795 + 4370006 * 2 ^ 59
def prefixEnd_4370006 : Nat := 4983230072969 + 3 ^ 40 * 4370006 * 2
def baseEnd_4370006 : Nat := 747971180343978188375905

theorem tailTrace_4370006 : CollatzResearch.WordTrace tailWord_4370006 prefixEnd_4370006 747971180343978188375905 := by
  unfold tailWord_4370006
  simp only [CollatzResearch.WordTrace]
  refine ⟨9961700812888879653183617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 106258142004148049633958581 9961700812888879653183617)
  ·
    refine ⟨7471275609666659739887713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9961700812888879653183617 7471275609666659739887713)
    ·
      refine ⟨5603456707249994804915785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7471275609666659739887713 5603456707249994804915785)
      ·
        refine ⟨4202592530437496103686839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5603456707249994804915785 4202592530437496103686839)
        ·
          refine ⟨6303888795656244155530259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4202592530437496103686839 6303888795656244155530259)
          ·
            refine ⟨9455833193484366233295389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6303888795656244155530259 9455833193484366233295389)
            ·
              refine ⟨3545937447556637337485771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9455833193484366233295389 3545937447556637337485771)
              ·
                refine ⟨5318906171334956006228657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3545937447556637337485771 5318906171334956006228657)
                ·
                  refine ⟨3989179628501217004671493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5318906171334956006228657 3989179628501217004671493)
                  ·
                    refine ⟨747971180343978188375905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3989179628501217004671493 747971180343978188375905)
                    ·
                      rfl

theorem cell23_4370006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_4370006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4370006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4370006 prefixEnd_4370006 := by exact prefixLift 4370006
  have htrace : WordTrace (prefixWord ++ tailWord_4370006) baseStart_4370006 baseEnd_4370006 := by
    simpa [prefixWord, tailWord_4370006, baseEnd_4370006] using wordTrace_append hprefix tailTrace_4370006
  have hstable : (prefixWord ++ tailWord_4370006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4370006).length < 2 ^ (prefixWord ++ tailWord_4370006).sum := by decide
  have hdescent : baseEnd_4370006 < baseStart_4370006 := by decide
  rcases family_descends (prefixWord ++ tailWord_4370006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4370038 : List Nat := [5, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5]
def baseStart_4370038 : Nat := 118140960795 + 4370038 * 2 ^ 59
def prefixEnd_4370038 : Nat := 4983230072969 + 3 ^ 40 * 4370038 * 2
def baseEnd_4370038 : Nat := 2243929972412878439927567

theorem tailTrace_4370038 : CollatzResearch.WordTrace tailWord_4370038 prefixEnd_4370038 2243929972412878439927567 := by
  unfold tailWord_4370038
  simp only [CollatzResearch.WordTrace]
  refine ⟨9961773758881633994756423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 106258920094737429277401845 9961773758881633994756423)
  ·
    refine ⟨14942660638322450992134635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9961773758881633994756423 14942660638322450992134635)
    ·
      refine ⟨22413990957483676488201953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14942660638322450992134635 22413990957483676488201953)
      ·
        refine ⟨16810493218112757366151465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22413990957483676488201953 16810493218112757366151465)
        ·
          refine ⟨12607869913584568024613599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16810493218112757366151465 12607869913584568024613599)
          ·
            refine ⟨18911804870376852036920399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12607869913584568024613599 18911804870376852036920399)
            ·
              refine ⟨28367707305565278055380599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18911804870376852036920399 28367707305565278055380599)
              ·
                refine ⟨42551560958347917083070899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28367707305565278055380599 42551560958347917083070899)
                ·
                  refine ⟨63827341437521875624606349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42551560958347917083070899 63827341437521875624606349)
                  ·
                    refine ⟨23935253039070703359227381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 63827341437521875624606349 23935253039070703359227381)
                    ·
                      refine ⟨2243929972412878439927567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23935253039070703359227381 2243929972412878439927567)
                      ·
                        rfl

theorem cell23_4370038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_4370038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4370038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4370038 prefixEnd_4370038 := by exact prefixLift 4370038
  have htrace : WordTrace (prefixWord ++ tailWord_4370038) baseStart_4370038 baseEnd_4370038 := by
    simpa [prefixWord, tailWord_4370038, baseEnd_4370038] using wordTrace_append hprefix tailTrace_4370038
  have hstable : (prefixWord ++ tailWord_4370038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4370038).length < 2 ^ (prefixWord ++ tailWord_4370038).sum := by decide
  have hdescent : baseEnd_4370038 < baseStart_4370038 := by decide
  rcases family_descends (prefixWord ++ tailWord_4370038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4370058 : List Nat := [3, 1, 2, 3, 2, 1, 3, 1, 7]
def baseStart_4370058 : Nat := 118140960795 + 4370058 * 2 ^ 59
def prefixEnd_4370058 : Nat := 4983230072969 + 3 ^ 40 * 4370058 * 2
def baseEnd_4370058 : Nat := 249326693558440929075275

theorem tailTrace_4370058 : CollatzResearch.WordTrace tailWord_4370058 prefixEnd_4370058 249326693558440929075275 := by
  unfold tailWord_4370058
  simp only [CollatzResearch.WordTrace]
  refine ⟨39847277400508421832957707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106259406401355791554553885 39847277400508421832957707)
  ·
    refine ⟨59770916100762632749436561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39847277400508421832957707 59770916100762632749436561)
    ·
      refine ⟨44828187075571974562077421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59770916100762632749436561 44828187075571974562077421)
      ·
        refine ⟨16810570153339490460779033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44828187075571974562077421 16810570153339490460779033)
        ·
          refine ⟨12607927615004617845584275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16810570153339490460779033 12607927615004617845584275)
          ·
            refine ⟨18911891422506926768376413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12607927615004617845584275 18911891422506926768376413)
            ·
              refine ⟨7091959283440097538141155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18911891422506926768376413 7091959283440097538141155)
              ·
                refine ⟨10637938925160146307211733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7091959283440097538141155 10637938925160146307211733)
                ·
                  refine ⟨249326693558440929075275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10637938925160146307211733 249326693558440929075275)
                  ·
                    rfl

theorem cell23_4370058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 1, 7].length) (baseStart_4370058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4370058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4370058 prefixEnd_4370058 := by exact prefixLift 4370058
  have htrace : WordTrace (prefixWord ++ tailWord_4370058) baseStart_4370058 baseEnd_4370058 := by
    simpa [prefixWord, tailWord_4370058, baseEnd_4370058] using wordTrace_append hprefix tailTrace_4370058
  have hstable : (prefixWord ++ tailWord_4370058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4370058).length < 2 ^ (prefixWord ++ tailWord_4370058).sum := by decide
  have hdescent : baseEnd_4370058 < baseStart_4370058 := by decide
  rcases family_descends (prefixWord ++ tailWord_4370058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4370111 : List Nat := [1, 1, 2, 2, 2, 3, 1, 1, 2, 3, 5]
def baseStart_4370111 : Nat := 118140960795 + 4370111 * 2 ^ 59
def prefixEnd_4370111 : Nat := 4983230072969 + 3 ^ 40 * 4370111 * 2
def baseEnd_4370111 : Nat := 2243967456500656654314731

theorem tailTrace_4370111 : CollatzResearch.WordTrace tailWord_4370111 prefixEnd_4370111 2243967456500656654314731 := by
  unfold tailWord_4370111
  simp only [CollatzResearch.WordTrace]
  refine ⟨159391042670841677383510187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106260695113894451589006791 159391042670841677383510187)
  ·
    refine ⟨239086564006262516075265281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159391042670841677383510187 239086564006262516075265281)
    ·
      refine ⟨179314923004696887056448961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 239086564006262516075265281 179314923004696887056448961)
      ·
        refine ⟨134486192253522665292336721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179314923004696887056448961 134486192253522665292336721)
        ·
          refine ⟨100864644190141998969252541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134486192253522665292336721 100864644190141998969252541)
          ·
            refine ⟨37824241571303249613469703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100864644190141998969252541 37824241571303249613469703)
            ·
              refine ⟨56736362356954874420204555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37824241571303249613469703 56736362356954874420204555)
              ·
                refine ⟨85104543535432311630306833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56736362356954874420204555 85104543535432311630306833)
                ·
                  refine ⟨63828407651574233722730125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85104543535432311630306833 63828407651574233722730125)
                  ·
                    refine ⟨23935652869340337646023797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 63828407651574233722730125 23935652869340337646023797)
                    ·
                      refine ⟨2243967456500656654314731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23935652869340337646023797 2243967456500656654314731)
                      ·
                        rfl

theorem cell23_4370111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 3, 5].length) (baseStart_4370111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4370111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4370111 prefixEnd_4370111 := by exact prefixLift 4370111
  have htrace : WordTrace (prefixWord ++ tailWord_4370111) baseStart_4370111 baseEnd_4370111 := by
    simpa [prefixWord, tailWord_4370111, baseEnd_4370111] using wordTrace_append hprefix tailTrace_4370111
  have hstable : (prefixWord ++ tailWord_4370111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4370111).length < 2 ^ (prefixWord ++ tailWord_4370111).sum := by decide
  have hdescent : baseEnd_4370111 < baseStart_4370111 := by decide
  rcases family_descends (prefixWord ++ tailWord_4370111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4370145 : List Nat := [1, 2, 3, 1, 5, 1, 1, 1, 1, 4, 3]
def baseStart_4370145 : Nat := 118140960795 + 4370145 * 2 ^ 59
def prefixEnd_4370145 : Nat := 4983230072969 + 3 ^ 40 * 4370145 * 2
def baseEnd_4370145 : Nat := 2243984914842909521289575

theorem tailTrace_4370145 : CollatzResearch.WordTrace tailWord_4370145 prefixEnd_4370145 2243984914842909521289575 := by
  unfold tailWord_4370145
  simp only [CollatzResearch.WordTrace]
  refine ⟨159392282752718501190247889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106261521835145667460165259 159392282752718501190247889)
  ·
    refine ⟨119544212064538875892685917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159392282752718501190247889 119544212064538875892685917)
    ·
      refine ⟨44829079524202078459757219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119544212064538875892685917 44829079524202078459757219)
      ·
        refine ⟨67243619286303117689635829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44829079524202078459757219 67243619286303117689635829)
        ·
          refine ⟨6304089308090917283403359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 67243619286303117689635829 6304089308090917283403359)
          ·
            refine ⟨9456133962136375925105039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6304089308090917283403359 9456133962136375925105039)
            ·
              refine ⟨14184200943204563887657559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9456133962136375925105039 14184200943204563887657559)
              ·
                refine ⟨21276301414806845831486339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14184200943204563887657559 21276301414806845831486339)
                ·
                  refine ⟨31914452122210268747229509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21276301414806845831486339 31914452122210268747229509)
                  ·
                    refine ⟨5983959772914425390105533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31914452122210268747229509 5983959772914425390105533)
                    ·
                      refine ⟨2243984914842909521289575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5983959772914425390105533 2243984914842909521289575)
                      ·
                        rfl

theorem cell23_4370145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 4, 3].length) (baseStart_4370145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4370145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4370145 prefixEnd_4370145 := by exact prefixLift 4370145
  have htrace : WordTrace (prefixWord ++ tailWord_4370145) baseStart_4370145 baseEnd_4370145 := by
    simpa [prefixWord, tailWord_4370145, baseEnd_4370145] using wordTrace_append hprefix tailTrace_4370145
  have hstable : (prefixWord ++ tailWord_4370145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4370145).length < 2 ^ (prefixWord ++ tailWord_4370145).sum := by decide
  have hdescent : baseEnd_4370145 < baseStart_4370145 := by decide
  rcases family_descends (prefixWord ++ tailWord_4370145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4370152 : List Nat := [2, 1, 4, 1, 3, 1, 1, 5, 1, 4]
def baseStart_4370152 : Nat := 118140960795 + 4370152 * 2 ^ 59
def prefixEnd_4370152 : Nat := 4983230072969 + 3 ^ 40 * 4370152 * 2
def baseEnd_4370152 : Nat := 747996169735830331300681

theorem tailTrace_4370152 : CollatzResearch.WordTrace tailWord_4370152 prefixEnd_4370152 747996169735830331300681 := by
  unfold tailWord_4370152
  simp only [CollatzResearch.WordTrace]
  refine ⟨79696269031846570692876355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106261692042462094257168473 79696269031846570692876355)
  ·
    refine ⟨119544403547769856039314533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79696269031846570692876355 119544403547769856039314533)
    ·
      refine ⟨22414575665206848007371475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 119544403547769856039314533 22414575665206848007371475)
      ·
        refine ⟨33621863497810272011057213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22414575665206848007371475 33621863497810272011057213)
        ·
          refine ⟨12608198811678852004146455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33621863497810272011057213 12608198811678852004146455)
          ·
            refine ⟨18912298217518278006219683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12608198811678852004146455 18912298217518278006219683)
            ·
              refine ⟨28368447326277417009329525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18912298217518278006219683 28368447326277417009329525)
              ·
                refine ⟨2659541936838507844624643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28368447326277417009329525 2659541936838507844624643)
                ·
                  refine ⟨3989312905257761766936965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2659541936838507844624643 3989312905257761766936965)
                  ·
                    refine ⟨747996169735830331300681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3989312905257761766936965 747996169735830331300681)
                    ·
                      rfl

theorem cell23_4370152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 5, 1, 4].length) (baseStart_4370152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4370152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4370152 prefixEnd_4370152 := by exact prefixLift 4370152
  have htrace : WordTrace (prefixWord ++ tailWord_4370152) baseStart_4370152 baseEnd_4370152 := by
    simpa [prefixWord, tailWord_4370152, baseEnd_4370152] using wordTrace_append hprefix tailTrace_4370152
  have hstable : (prefixWord ++ tailWord_4370152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4370152).length < 2 ^ (prefixWord ++ tailWord_4370152).sum := by decide
  have hdescent : baseEnd_4370152 < baseStart_4370152 := by decide
  rcases family_descends (prefixWord ++ tailWord_4370152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4370171 : List Nat := [1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 7]
def baseStart_4370171 : Nat := 118140960795 + 4370171 * 2 ^ 59
def prefixEnd_4370171 : Nat := 4983230072969 + 3 ^ 40 * 4370171 * 2
def baseEnd_4370171 : Nat := 2243998265339926419564455

theorem tailTrace_4370171 : CollatzResearch.WordTrace tailWord_4370171 prefixEnd_4370171 2243998265339926419564455 := by
  unfold tailWord_4370171
  simp only [CollatzResearch.WordTrace]
  refine ⟨159393231050624307630694367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106262154033749538420462911 159393231050624307630694367)
  ·
    refine ⟨239089846575936461446041551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159393231050624307630694367 239089846575936461446041551)
    ·
      refine ⟨358634769863904692169062327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239089846575936461446041551 358634769863904692169062327)
      ·
        refine ⟨537952154795857038253593491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 358634769863904692169062327 537952154795857038253593491)
        ·
          refine ⟨806928232193785557380390237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 537952154795857038253593491 806928232193785557380390237)
          ·
            refine ⟨302598087072669584017646339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 806928232193785557380390237 302598087072669584017646339)
            ·
              refine ⟨453897130609004376026469509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 302598087072669584017646339 453897130609004376026469509)
              ·
                refine ⟨85105711989188320504963033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 453897130609004376026469509 85105711989188320504963033)
                ·
                  refine ⟨63829283991891240378722275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85105711989188320504963033 63829283991891240378722275)
                  ·
                    refine ⟨95743925987836860568083413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 63829283991891240378722275 95743925987836860568083413)
                    ·
                      refine ⟨2243998265339926419564455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 95743925987836860568083413 2243998265339926419564455)
                      ·
                        rfl

theorem cell23_4370171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 7].length) (baseStart_4370171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4370171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4370171 prefixEnd_4370171 := by exact prefixLift 4370171
  have htrace : WordTrace (prefixWord ++ tailWord_4370171) baseStart_4370171 baseEnd_4370171 := by
    simpa [prefixWord, tailWord_4370171, baseEnd_4370171] using wordTrace_append hprefix tailTrace_4370171
  have hstable : (prefixWord ++ tailWord_4370171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4370171).length < 2 ^ (prefixWord ++ tailWord_4370171).sum := by decide
  have hdescent : baseEnd_4370171 < baseStart_4370171 := by decide
  rcases family_descends (prefixWord ++ tailWord_4370171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4370175 : List Nat := [1, 1, 2, 2, 1, 3, 3, 3, 3, 1, 3]
def baseStart_4370175 : Nat := 118140960795 + 4370175 * 2 ^ 59
def prefixEnd_4370175 : Nat := 4983230072969 + 3 ^ 40 * 4370175 * 2
def baseEnd_4370175 : Nat := 2244000319262544403914437

theorem tailTrace_4370175 : CollatzResearch.WordTrace tailWord_4370175 prefixEnd_4370175 2244000319262544403914437 := by
  unfold tailWord_4370175
  simp only [CollatzResearch.WordTrace]
  refine ⟨159393376942609816313839979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106262251295073210875893319 159393376942609816313839979)
  ·
    refine ⟨239090065413914724470759969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159393376942609816313839979 239090065413914724470759969)
    ·
      refine ⟨179317549060436043353069977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 239090065413914724470759969 179317549060436043353069977)
      ·
        refine ⟨134488161795327032514802483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179317549060436043353069977 134488161795327032514802483)
        ·
          refine ⟨201732242692990548772203725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134488161795327032514802483 201732242692990548772203725)
          ·
            refine ⟨75649591009871455789576397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 201732242692990548772203725 75649591009871455789576397)
            ·
              refine ⟨28368596628701795921091149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75649591009871455789576397 28368596628701795921091149)
              ·
                refine ⟨10638223735763173470409181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28368596628701795921091149 10638223735763173470409181)
                ·
                  refine ⟨3989333900911190051403443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10638223735763173470409181 3989333900911190051403443)
                  ·
                    refine ⟨5984000851366785077105165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3989333900911190051403443 5984000851366785077105165)
                    ·
                      refine ⟨2244000319262544403914437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5984000851366785077105165 2244000319262544403914437)
                      ·
                        rfl

theorem cell23_4370175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 3, 3, 1, 3].length) (baseStart_4370175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4370175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4370175 prefixEnd_4370175 := by exact prefixLift 4370175
  have htrace : WordTrace (prefixWord ++ tailWord_4370175) baseStart_4370175 baseEnd_4370175 := by
    simpa [prefixWord, tailWord_4370175, baseEnd_4370175] using wordTrace_append hprefix tailTrace_4370175
  have hstable : (prefixWord ++ tailWord_4370175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4370175).length < 2 ^ (prefixWord ++ tailWord_4370175).sum := by decide
  have hdescent : baseEnd_4370175 < baseStart_4370175 := by decide
  rcases family_descends (prefixWord ++ tailWord_4370175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4370208 : List Nat := [2, 1, 1, 5, 1, 1, 2, 1, 3, 6]
def baseStart_4370208 : Nat := 118140960795 + 4370208 * 2 ^ 59
def prefixEnd_4370208 : Nat := 4983230072969 + 3 ^ 40 * 4370208 * 2
def baseEnd_4370208 : Nat := 748005754708047591600595

theorem tailTrace_4370208 : CollatzResearch.WordTrace tailWord_4370208 prefixEnd_4370208 748005754708047591600595 := by
  unfold tailWord_4370208
  simp only [CollatzResearch.WordTrace]
  refine ⟨79697290275745131474895639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106263053700993508633194185 79697290275745131474895639)
  ·
    refine ⟨119545935413617697212343459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79697290275745131474895639 119545935413617697212343459)
    ·
      refine ⟨179318903120426545818515189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119545935413617697212343459 179318903120426545818515189)
      ·
        refine ⟨16811147167539988670485799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 179318903120426545818515189 16811147167539988670485799)
        ·
          refine ⟨25216720751309983005728699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16811147167539988670485799 25216720751309983005728699)
          ·
            refine ⟨37825081126964974508593049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25216720751309983005728699 37825081126964974508593049)
            ·
              refine ⟨28368810845223730881444787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37825081126964974508593049 28368810845223730881444787)
              ·
                refine ⟨42553216267835596322167181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28368810845223730881444787 42553216267835596322167181)
                ·
                  refine ⟨15957456100438348620812693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42553216267835596322167181 15957456100438348620812693)
                  ·
                    refine ⟨748005754708047591600595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15957456100438348620812693 748005754708047591600595)
                    ·
                      rfl

theorem cell23_4370208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 3, 6].length) (baseStart_4370208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4370208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4370208 prefixEnd_4370208 := by exact prefixLift 4370208
  have htrace : WordTrace (prefixWord ++ tailWord_4370208) baseStart_4370208 baseEnd_4370208 := by
    simpa [prefixWord, tailWord_4370208, baseEnd_4370208] using wordTrace_append hprefix tailTrace_4370208
  have hstable : (prefixWord ++ tailWord_4370208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4370208).length < 2 ^ (prefixWord ++ tailWord_4370208).sum := by decide
  have hdescent : baseEnd_4370208 < baseStart_4370208 := by decide
  rcases family_descends (prefixWord ++ tailWord_4370208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4370209 : List Nat := [1, 2, 3, 2, 1, 3, 3, 3, 1, 1, 3]
def baseStart_4370209 : Nat := 118140960795 + 4370209 * 2 ^ 59
def prefixEnd_4370209 : Nat := 4983230072969 + 3 ^ 40 * 4370209 * 2
def baseEnd_4370209 : Nat := 2244017777604797270889281

theorem tailTrace_4370209 : CollatzResearch.WordTrace tailWord_4370209 prefixEnd_4370209 2244017777604797270889281 := by
  unfold tailWord_4370209
  simp only [CollatzResearch.WordTrace]
  refine ⟨159394617024486640120577681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106263078016324426747051787 159394617024486640120577681)
  ·
    refine ⟨119545962768364980090433261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159394617024486640120577681 119545962768364980090433261)
    ·
      refine ⟨44829736038136867533912473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119545962768364980090433261 44829736038136867533912473)
      ·
        refine ⟨33622302028602650650434355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44829736038136867533912473 33622302028602650650434355)
        ·
          refine ⟨50433453042903975975651533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33622302028602650650434355 50433453042903975975651533)
          ·
            refine ⟨18912544891088990990869325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50433453042903975975651533 18912544891088990990869325)
            ·
              refine ⟨7092204334158371621575997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18912544891088990990869325 7092204334158371621575997)
              ·
                refine ⟨2659576625309389358090999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7092204334158371621575997 2659576625309389358090999)
                ·
                  refine ⟨3989364937964084037136499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2659576625309389358090999 3989364937964084037136499)
                  ·
                    refine ⟨5984047406946126055704749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3989364937964084037136499 5984047406946126055704749)
                    ·
                      refine ⟨2244017777604797270889281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5984047406946126055704749 2244017777604797270889281)
                      ·
                        rfl

theorem cell23_4370209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 3, 1, 1, 3].length) (baseStart_4370209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4370209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4370209 prefixEnd_4370209 := by exact prefixLift 4370209
  have htrace : WordTrace (prefixWord ++ tailWord_4370209) baseStart_4370209 baseEnd_4370209 := by
    simpa [prefixWord, tailWord_4370209, baseEnd_4370209] using wordTrace_append hprefix tailTrace_4370209
  have hstable : (prefixWord ++ tailWord_4370209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4370209).length < 2 ^ (prefixWord ++ tailWord_4370209).sum := by decide
  have hdescent : baseEnd_4370209 < baseStart_4370209 := by decide
  rcases family_descends (prefixWord ++ tailWord_4370209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4370225 : List Nat := [1, 2, 2, 3, 2, 2, 2, 1, 4, 4]
def baseStart_4370225 : Nat := 118140960795 + 4370225 * 2 ^ 59
def prefixEnd_4370225 : Nat := 4983230072969 + 3 ^ 40 * 4370225 * 2
def baseEnd_4370225 : Nat := 748008664431756402763069

theorem tailTrace_4370225 : CollatzResearch.WordTrace tailWord_4370225 prefixEnd_4370225 748008664431756402763069 := by
  unfold tailWord_4370225
  simp only [CollatzResearch.WordTrace]
  refine ⟨159395200592428674853160129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106263467061619116568773419 159395200592428674853160129)
  ·
    refine ⟨119546400444321506139870097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159395200592428674853160129 119546400444321506139870097)
    ·
      refine ⟨89659800333241129604902573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119546400444321506139870097 89659800333241129604902573)
      ·
        refine ⟨33622425124965423601838465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89659800333241129604902573 33622425124965423601838465)
        ·
          refine ⟨25216818843724067701378849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33622425124965423601838465 25216818843724067701378849)
          ·
            refine ⟨18912614132793050776034137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25216818843724067701378849 18912614132793050776034137)
            ·
              refine ⟨14184460599594788082025603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18912614132793050776034137 14184460599594788082025603)
              ·
                refine ⟨21276690899392182123038405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14184460599594788082025603 21276690899392182123038405)
                ·
                  refine ⟨3989379543636034148069701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21276690899392182123038405 3989379543636034148069701)
                  ·
                    refine ⟨748008664431756402763069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3989379543636034148069701 748008664431756402763069)
                    ·
                      rfl

theorem cell23_4370225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 4, 4].length) (baseStart_4370225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4370225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4370225 prefixEnd_4370225 := by exact prefixLift 4370225
  have htrace : WordTrace (prefixWord ++ tailWord_4370225) baseStart_4370225 baseEnd_4370225 := by
    simpa [prefixWord, tailWord_4370225, baseEnd_4370225] using wordTrace_append hprefix tailTrace_4370225
  have hstable : (prefixWord ++ tailWord_4370225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4370225).length < 2 ^ (prefixWord ++ tailWord_4370225).sum := by decide
  have hdescent : baseEnd_4370225 < baseStart_4370225 := by decide
  rcases family_descends (prefixWord ++ tailWord_4370225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4370226 : List Nat := [3, 2, 1, 1, 3, 3, 3, 2, 1, 1, 3]
def baseStart_4370226 : Nat := 118140960795 + 4370226 * 2 ^ 59
def prefixEnd_4370226 : Nat := 4983230072969 + 3 ^ 40 * 4370226 * 2
def baseEnd_4370226 : Nat := 2244026506775923704376703

theorem tailTrace_4370226 : CollatzResearch.WordTrace tailWord_4370226 prefixEnd_4370226 2244026506775923704376703 := by
  unfold tailWord_4370226
  simp only [CollatzResearch.WordTrace]
  refine ⟨39848809266356263005986633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106263491376950034682631021 39848809266356263005986633)
  ·
    refine ⟨29886606949767197254489975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39848809266356263005986633 29886606949767197254489975)
    ·
      refine ⟨44829910424650795881734963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29886606949767197254489975 44829910424650795881734963)
      ·
        refine ⟨67244865636976193822602445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44829910424650795881734963 67244865636976193822602445)
        ·
          refine ⟨25216824613866072683475917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67244865636976193822602445 25216824613866072683475917)
          ·
            refine ⟨9456309230199777256303469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25216824613866072683475917 9456309230199777256303469)
            ·
              refine ⟨3546115961324916471113801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9456309230199777256303469 3546115961324916471113801)
              ·
                refine ⟨2659586970993687353335351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3546115961324916471113801 2659586970993687353335351)
                ·
                  refine ⟨3989380456490531030003027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2659586970993687353335351 3989380456490531030003027)
                  ·
                    refine ⟨5984070684735796545004541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3989380456490531030003027 5984070684735796545004541)
                    ·
                      refine ⟨2244026506775923704376703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5984070684735796545004541 2244026506775923704376703)
                      ·
                        rfl

theorem cell23_4370226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 3, 2, 1, 1, 3].length) (baseStart_4370226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4370226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4370226 prefixEnd_4370226 := by exact prefixLift 4370226
  have htrace : WordTrace (prefixWord ++ tailWord_4370226) baseStart_4370226 baseEnd_4370226 := by
    simpa [prefixWord, tailWord_4370226, baseEnd_4370226] using wordTrace_append hprefix tailTrace_4370226
  have hstable : (prefixWord ++ tailWord_4370226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4370226).length < 2 ^ (prefixWord ++ tailWord_4370226).sum := by decide
  have hdescent : baseEnd_4370226 < baseStart_4370226 := by decide
  rcases family_descends (prefixWord ++ tailWord_4370226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4370246 : List Nat := [6, 1, 1, 2, 1, 3, 1, 2, 1, 5]
def baseStart_4370246 : Nat := 118140960795 + 4370246 * 2 ^ 59
def prefixEnd_4370246 : Nat := 4983230072969 + 3 ^ 40 * 4370246 * 2
def baseEnd_4370246 : Nat := 748012258796337875375537

theorem tailTrace_4370246 : CollatzResearch.WordTrace tailWord_4370246 prefixEnd_4370246 748012258796337875375537 := by
  unfold tailWord_4370246
  simp only [CollatzResearch.WordTrace]
  refine ⟨4981123953917268607489831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 106263977683568396959783061 4981123953917268607489831)
  ·
    refine ⟨7471685930875902911234747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4981123953917268607489831 7471685930875902911234747)
    ·
      refine ⟨11207528896313854366852121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7471685930875902911234747 11207528896313854366852121)
      ·
        refine ⟨8405646672235390775139091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11207528896313854366852121 8405646672235390775139091)
        ·
          refine ⟨12608470008353086162708637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8405646672235390775139091 12608470008353086162708637)
          ·
            refine ⟨4728176253132407311015739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12608470008353086162708637 4728176253132407311015739)
            ·
              refine ⟨7092264379698610966523609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4728176253132407311015739 7092264379698610966523609)
              ·
                refine ⟨5319198284773958224892707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7092264379698610966523609 5319198284773958224892707)
                ·
                  refine ⟨7978797427160937337339061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5319198284773958224892707 7978797427160937337339061)
                  ·
                    refine ⟨748012258796337875375537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7978797427160937337339061 748012258796337875375537)
                    ·
                      rfl

theorem cell23_4370246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_4370246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4370246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4370246 prefixEnd_4370246 := by exact prefixLift 4370246
  have htrace : WordTrace (prefixWord ++ tailWord_4370246) baseStart_4370246 baseEnd_4370246 := by
    simpa [prefixWord, tailWord_4370246, baseEnd_4370246] using wordTrace_append hprefix tailTrace_4370246
  have hstable : (prefixWord ++ tailWord_4370246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4370246).length < 2 ^ (prefixWord ++ tailWord_4370246).sum := by decide
  have hdescent : baseEnd_4370246 < baseStart_4370246 := by decide
  rcases family_descends (prefixWord ++ tailWord_4370246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4370252 : List Nat := [2, 2, 1, 3, 4, 1, 1, 1, 3, 2, 3]
def baseStart_4370252 : Nat := 118140960795 + 4370252 * 2 ^ 59
def prefixEnd_4370252 : Nat := 4983230072969 + 3 ^ 40 * 4370252 * 2
def baseEnd_4370252 : Nat := 2244039857272940602651583

theorem tailTrace_4370252 : CollatzResearch.WordTrace tailWord_4370252 prefixEnd_4370252 2244039857272940602651583 := by
  unfold tailWord_4370252
  simp only [CollatzResearch.WordTrace]
  refine ⟨79698092681665429232196505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106264123575553905642928673 79698092681665429232196505)
  ·
    refine ⟨59773569511249071924147379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79698092681665429232196505 59773569511249071924147379)
    ·
      refine ⟨89660354266873607886221069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59773569511249071924147379 89660354266873607886221069)
      ·
        refine ⟨33622632850077602957332901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89660354266873607886221069 33622632850077602957332901)
        ·
          refine ⟨6304243659389550554499919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33622632850077602957332901 6304243659389550554499919)
          ·
            refine ⟨9456365489084325831749879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6304243659389550554499919 9456365489084325831749879)
            ·
              refine ⟨14184548233626488747624819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9456365489084325831749879 14184548233626488747624819)
              ·
                refine ⟨21276822350439733121437229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14184548233626488747624819 21276822350439733121437229)
                ·
                  refine ⟨7978808381414899920538961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21276822350439733121437229 7978808381414899920538961)
                  ·
                    refine ⟨5984106286061174940404221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7978808381414899920538961 5984106286061174940404221)
                    ·
                      refine ⟨2244039857272940602651583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5984106286061174940404221 2244039857272940602651583)
                      ·
                        rfl

theorem cell23_4370252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 3, 2, 3].length) (baseStart_4370252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4370252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4370252 prefixEnd_4370252 := by exact prefixLift 4370252
  have htrace : WordTrace (prefixWord ++ tailWord_4370252) baseStart_4370252 baseEnd_4370252 := by
    simpa [prefixWord, tailWord_4370252, baseEnd_4370252] using wordTrace_append hprefix tailTrace_4370252
  have hstable : (prefixWord ++ tailWord_4370252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4370252).length < 2 ^ (prefixWord ++ tailWord_4370252).sum := by decide
  have hdescent : baseEnd_4370252 < baseStart_4370252 := by decide
  rcases family_descends (prefixWord ++ tailWord_4370252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4370265 : List Nat := [1, 2, 1, 2, 2, 3, 3, 2, 1, 3, 3]
def baseStart_4370265 : Nat := 118140960795 + 4370265 * 2 ^ 59
def prefixEnd_4370265 : Nat := 4983230072969 + 3 ^ 40 * 4370265 * 2
def baseEnd_4370265 : Nat := 2244046532521449051789023

theorem tailTrace_4370265 : CollatzResearch.WordTrace tailWord_4370265 prefixEnd_4370265 2244046532521449051789023 := by
  unfold tailWord_4370265
  simp only [CollatzResearch.WordTrace]
  refine ⟨159396659512283761684616249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106264439674855841123077499 159396659512283761684616249)
  ·
    refine ⟨119547494634212821263462187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159396659512283761684616249 119547494634212821263462187)
    ·
      refine ⟨179321241951319231895193281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119547494634212821263462187 179321241951319231895193281)
      ·
        refine ⟨134490931463489423921394961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179321241951319231895193281 134490931463489423921394961)
        ·
          refine ⟨100868198597617067941046221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134490931463489423921394961 100868198597617067941046221)
          ·
            refine ⟨37825574474106400477892333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100868198597617067941046221 37825574474106400477892333)
            ·
              refine ⟨14184590427789900179209625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37825574474106400477892333 14184590427789900179209625)
              ·
                refine ⟨10638442820842425134407219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14184590427789900179209625 10638442820842425134407219)
                ·
                  refine ⟨15957664231263637701610829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10638442820842425134407219 15957664231263637701610829)
                  ·
                    refine ⟨5984124086723864138104061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15957664231263637701610829 5984124086723864138104061)
                    ·
                      refine ⟨2244046532521449051789023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5984124086723864138104061 2244046532521449051789023)
                      ·
                        rfl

theorem cell23_4370265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 2, 1, 3, 3].length) (baseStart_4370265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4370265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4370265 prefixEnd_4370265 := by exact prefixLift 4370265
  have htrace : WordTrace (prefixWord ++ tailWord_4370265) baseStart_4370265 baseEnd_4370265 := by
    simpa [prefixWord, tailWord_4370265, baseEnd_4370265] using wordTrace_append hprefix tailTrace_4370265
  have hstable : (prefixWord ++ tailWord_4370265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4370265).length < 2 ^ (prefixWord ++ tailWord_4370265).sum := by decide
  have hdescent : baseEnd_4370265 < baseStart_4370265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4370265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4370298 : List Nat := [3, 1, 1, 1, 1, 1, 5, 1, 1, 8]
def baseStart_4370298 : Nat := 118140960795 + 4370298 * 2 ^ 59
def prefixEnd_4370298 : Nat := 4983230072969 + 3 ^ 40 * 4370298 * 2
def baseEnd_4370298 : Nat := 748021159127682474225457

theorem tailTrace_4370298 : CollatzResearch.WordTrace tailWord_4370298 prefixEnd_4370298 748021159127682474225457 := by
  unfold tailWord_4370298
  simp only [CollatzResearch.WordTrace]
  refine ⟨39849465780291052080141887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106265242080776138880378365 39849465780291052080141887)
  ·
    refine ⟨59774198670436578120212831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39849465780291052080141887 59774198670436578120212831)
    ·
      refine ⟨89661298005654867180319247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59774198670436578120212831 89661298005654867180319247)
      ·
        refine ⟨134491947008482300770478871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89661298005654867180319247 134491947008482300770478871)
        ·
          refine ⟨201737920512723451155718307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134491947008482300770478871 201737920512723451155718307)
          ·
            refine ⟨302606880769085176733577461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201737920512723451155718307 302606880769085176733577461)
            ·
              refine ⟨28369395072101735318772887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 302606880769085176733577461 28369395072101735318772887)
              ·
                refine ⟨42554092608152602978159331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28369395072101735318772887 42554092608152602978159331)
                ·
                  refine ⟨63831138912228904467238997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42554092608152602978159331 63831138912228904467238997)
                  ·
                    refine ⟨748021159127682474225457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 63831138912228904467238997 748021159127682474225457)
                    ·
                      rfl

theorem cell23_4370298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 1, 8].length) (baseStart_4370298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4370298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4370298 prefixEnd_4370298 := by exact prefixLift 4370298
  have htrace : WordTrace (prefixWord ++ tailWord_4370298) baseStart_4370298 baseEnd_4370298 := by
    simpa [prefixWord, tailWord_4370298, baseEnd_4370298] using wordTrace_append hprefix tailTrace_4370298
  have hstable : (prefixWord ++ tailWord_4370298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4370298).length < 2 ^ (prefixWord ++ tailWord_4370298).sum := by decide
  have hdescent : baseEnd_4370298 < baseStart_4370298 := by decide
  rcases family_descends (prefixWord ++ tailWord_4370298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4370348 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 8]
def baseStart_4370348 : Nat := 118140960795 + 4370348 * 2 ^ 59
def prefixEnd_4370348 : Nat := 4983230072969 + 3 ^ 40 * 4370348 * 2
def baseEnd_4370348 : Nat := 2244089151415772227051141

theorem tailTrace_4370348 : CollatzResearch.WordTrace tailWord_4370348 prefixEnd_4370348 2244089151415772227051141 := by
  unfold tailWord_4370348
  simp only [CollatzResearch.WordTrace]
  refine ⟨79699843385491533429943849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106266457847322044573258465 79699843385491533429943849)
  ·
    refine ⟨59774882539118650072457887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79699843385491533429943849 59774882539118650072457887)
    ·
      refine ⟨89662323808677975108686831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59774882539118650072457887 89662323808677975108686831)
      ·
        refine ⟨134493485713016962663030247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89662323808677975108686831 134493485713016962663030247)
        ·
          refine ⟨201740228569525443994545371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134493485713016962663030247 201740228569525443994545371)
          ·
            refine ⟨302610342854288165991818057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201740228569525443994545371 302610342854288165991818057)
            ·
              refine ⟨226957757140716124493863543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 302610342854288165991818057 226957757140716124493863543)
              ·
                refine ⟨340436635711074186740795315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 226957757140716124493863543 340436635711074186740795315)
                ·
                  refine ⟨510654953566611280111192973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 340436635711074186740795315 510654953566611280111192973)
                  ·
                    refine ⟨191495607587479230041697365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 510654953566611280111192973 191495607587479230041697365)
                    ·
                      refine ⟨2244089151415772227051141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 191495607587479230041697365 2244089151415772227051141)
                      ·
                        rfl

theorem cell23_4370348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 8].length) (baseStart_4370348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4370348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4370348 prefixEnd_4370348 := by exact prefixLift 4370348
  have htrace : WordTrace (prefixWord ++ tailWord_4370348) baseStart_4370348 baseEnd_4370348 := by
    simpa [prefixWord, tailWord_4370348, baseEnd_4370348] using wordTrace_append hprefix tailTrace_4370348
  have hstable : (prefixWord ++ tailWord_4370348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4370348).length < 2 ^ (prefixWord ++ tailWord_4370348).sum := by decide
  have hdescent : baseEnd_4370348 < baseStart_4370348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4370348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4370350 : List Nat := [4, 1, 5, 1, 2, 1, 1, 1, 1, 3, 3]
def baseStart_4370350 : Nat := 118140960795 + 4370350 * 2 ^ 59
def prefixEnd_4370350 : Nat := 4983230072969 + 3 ^ 40 * 4370350 * 2
def baseEnd_4370350 : Nat := 2244090178377081219226133

theorem tailTrace_4370350 : CollatzResearch.WordTrace tailWord_4370350 prefixEnd_4370350 2244090178377081219226133 := by
  unfold tailWord_4370350
  simp only [CollatzResearch.WordTrace]
  refine ⟨19924969964621977650182563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106266506477983880800973669 19924969964621977650182563)
  ·
    refine ⟨29887454946932966475273845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19924969964621977650182563 29887454946932966475273845)
    ·
      refine ⟨2801948901274965607056923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29887454946932966475273845 2801948901274965607056923)
      ·
        refine ⟨4202923351912448410585385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2801948901274965607056923 4202923351912448410585385)
        ·
          refine ⟨3152192513934336307939039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4202923351912448410585385 3152192513934336307939039)
          ·
            refine ⟨4728288770901504461908559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3152192513934336307939039 4728288770901504461908559)
            ·
              refine ⟨7092433156352256692862839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4728288770901504461908559 7092433156352256692862839)
              ·
                refine ⟨10638649734528385039294259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7092433156352256692862839 10638649734528385039294259)
                ·
                  refine ⟨15957974601792577558941389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10638649734528385039294259 15957974601792577558941389)
                  ·
                    refine ⟨5984240475672216584603021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15957974601792577558941389 5984240475672216584603021)
                    ·
                      refine ⟨2244090178377081219226133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5984240475672216584603021 2244090178377081219226133)
                      ·
                        rfl

theorem cell23_4370350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_4370350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4370350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4370350 prefixEnd_4370350 := by exact prefixLift 4370350
  have htrace : WordTrace (prefixWord ++ tailWord_4370350) baseStart_4370350 baseEnd_4370350 := by
    simpa [prefixWord, tailWord_4370350, baseEnd_4370350] using wordTrace_append hprefix tailTrace_4370350
  have hstable : (prefixWord ++ tailWord_4370350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4370350).length < 2 ^ (prefixWord ++ tailWord_4370350).sum := by decide
  have hdescent : baseEnd_4370350 < baseStart_4370350 := by decide
  rcases family_descends (prefixWord ++ tailWord_4370350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4370355 : List Nat := [1, 1, 1, 2, 3, 1, 3, 3, 2, 3, 3]
def baseStart_4370355 : Nat := 118140960795 + 4370355 * 2 ^ 59
def prefixEnd_4370355 : Nat := 4983230072969 + 3 ^ 40 * 4370355 * 2
def baseEnd_4370355 : Nat := 2244092745780353699663609

theorem tailTrace_4370355 : CollatzResearch.WordTrace tailWord_4370355 prefixEnd_4370355 2244092745780353699663609 := by
  unfold tailWord_4370355
  simp only [CollatzResearch.WordTrace]
  refine ⟨159399942081957707055392519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106266628054638471370261679 159399942081957707055392519)
  ·
    refine ⟨239099913122936560583088779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159399942081957707055392519 239099913122936560583088779)
    ·
      refine ⟨358649869684404840874633169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239099913122936560583088779 358649869684404840874633169)
      ·
        refine ⟨268987402263303630655974877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 358649869684404840874633169 268987402263303630655974877)
        ·
          refine ⟨100870275848738861495990579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 268987402263303630655974877 100870275848738861495990579)
          ·
            refine ⟨151305413773108292243985869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100870275848738861495990579 151305413773108292243985869)
            ·
              refine ⟨56739530164915609591494701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 151305413773108292243985869 56739530164915609591494701)
              ·
                refine ⟨21277323811843353596810513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56739530164915609591494701 21277323811843353596810513)
                ·
                  refine ⟨15957992858882515197607885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21277323811843353596810513 15957992858882515197607885)
                  ·
                    refine ⟨5984247322080943199102957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15957992858882515197607885 5984247322080943199102957)
                    ·
                      refine ⟨2244092745780353699663609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5984247322080943199102957 2244092745780353699663609)
                      ·
                        rfl

theorem cell23_4370355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 2, 3, 3].length) (baseStart_4370355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4370355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4370355 prefixEnd_4370355 := by exact prefixLift 4370355
  have htrace : WordTrace (prefixWord ++ tailWord_4370355) baseStart_4370355 baseEnd_4370355 := by
    simpa [prefixWord, tailWord_4370355, baseEnd_4370355] using wordTrace_append hprefix tailTrace_4370355
  have hstable : (prefixWord ++ tailWord_4370355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4370355).length < 2 ^ (prefixWord ++ tailWord_4370355).sum := by decide
  have hdescent : baseEnd_4370355 < baseStart_4370355 := by decide
  rcases family_descends (prefixWord ++ tailWord_4370355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4370375 : List Nat := [1, 1, 4, 1, 1, 2, 1, 5, 2, 5]
def baseStart_4370375 : Nat := 118140960795 + 4370375 * 2 ^ 59
def prefixEnd_4370375 : Nat := 4983230072969 + 3 ^ 40 * 4370375 * 2
def baseEnd_4370375 : Nat := 748034338464481207137839

theorem tailTrace_4370375 : CollatzResearch.WordTrace tailWord_4370375 prefixEnd_4370375 748034338464481207137839 := by
  unfold tailWord_4370375
  simp only [CollatzResearch.WordTrace]
  refine ⟨159400671541885250471120579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106267114361256833647413719 159400671541885250471120579)
  ·
    refine ⟨239101007312827875706680869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159400671541885250471120579 239101007312827875706680869)
    ·
      refine ⟨44831438871155226695002663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 239101007312827875706680869 44831438871155226695002663)
      ·
        refine ⟨67247158306732840042503995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44831438871155226695002663 67247158306732840042503995)
        ·
          refine ⟨100870737460099260063755993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67247158306732840042503995 100870737460099260063755993)
          ·
            refine ⟨75653053095074445047816995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100870737460099260063755993 75653053095074445047816995)
            ·
              refine ⟨113479579642611667571725493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75653053095074445047816995 113479579642611667571725493)
              ·
                refine ⟨10638710591494843834849265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 113479579642611667571725493 10638710591494843834849265)
                ·
                  refine ⟨7979032943621132876136949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10638710591494843834849265 7979032943621132876136949)
                  ·
                    refine ⟨748034338464481207137839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7979032943621132876136949 748034338464481207137839)
                    ·
                      rfl

theorem cell23_4370375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 5, 2, 5].length) (baseStart_4370375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4370375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4370375 prefixEnd_4370375 := by exact prefixLift 4370375
  have htrace : WordTrace (prefixWord ++ tailWord_4370375) baseStart_4370375 baseEnd_4370375 := by
    simpa [prefixWord, tailWord_4370375, baseEnd_4370375] using wordTrace_append hprefix tailTrace_4370375
  have hstable : (prefixWord ++ tailWord_4370375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4370375).length < 2 ^ (prefixWord ++ tailWord_4370375).sum := by decide
  have hdescent : baseEnd_4370375 < baseStart_4370375 := by decide
  rcases family_descends (prefixWord ++ tailWord_4370375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4370412 : List Nat := [2, 2, 1, 1, 2, 1, 1, 5, 2, 4, 2]
def baseStart_4370412 : Nat := 118140960795 + 4370412 * 2 ^ 59
def prefixEnd_4370412 : Nat := 4983230072969 + 3 ^ 40 * 4370412 * 2
def baseEnd_4370412 : Nat := 2244122014177659976650847

theorem tailTrace_4370412 : CollatzResearch.WordTrace tailWord_4370412 prefixEnd_4370412 2244122014177659976650847 := by
  unfold tailWord_4370412
  simp only [CollatzResearch.WordTrace]
  refine ⟨79701010521375602895108745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106268014028500803860144993 79701010521375602895108745)
  ·
    refine ⟨59775757891031702171331559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79701010521375602895108745 59775757891031702171331559)
    ·
      refine ⟨89663636836547553256997339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59775757891031702171331559 89663636836547553256997339)
      ·
        refine ⟨134495455254821329885496009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89663636836547553256997339 134495455254821329885496009)
        ·
          refine ⟨100871591441115997414122007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134495455254821329885496009 100871591441115997414122007)
          ·
            refine ⟨151307387161673996121183011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100871591441115997414122007 151307387161673996121183011)
            ·
              refine ⟨226961080742510994181774517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151307387161673996121183011 226961080742510994181774517)
              ·
                refine ⟨21277601319610405704541361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 226961080742510994181774517 21277601319610405704541361)
                ·
                  refine ⟨15958200989707804278406021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21277601319610405704541361 15958200989707804278406021)
                  ·
                    refine ⟨2992162685570213302201129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15958200989707804278406021 2992162685570213302201129)
                    ·
                      refine ⟨2244122014177659976650847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2992162685570213302201129 2244122014177659976650847)
                      ·
                        rfl

theorem cell23_4370412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 4, 2].length) (baseStart_4370412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4370412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4370412 prefixEnd_4370412 := by exact prefixLift 4370412
  have htrace : WordTrace (prefixWord ++ tailWord_4370412) baseStart_4370412 baseEnd_4370412 := by
    simpa [prefixWord, tailWord_4370412, baseEnd_4370412] using wordTrace_append hprefix tailTrace_4370412
  have hstable : (prefixWord ++ tailWord_4370412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4370412).length < 2 ^ (prefixWord ++ tailWord_4370412).sum := by decide
  have hdescent : baseEnd_4370412 < baseStart_4370412 := by decide
  rcases family_descends (prefixWord ++ tailWord_4370412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4370482 : List Nat := [3, 2, 1, 1, 2, 3, 2, 1, 3, 5]
def baseStart_4370482 : Nat := 118140960795 + 4370482 * 2 ^ 59
def prefixEnd_4370482 : Nat := 4983230072969 + 3 ^ 40 * 4370482 * 2
def baseEnd_4370482 : Nat := 748052652607824900925175

theorem tailTrace_4370482 : CollatzResearch.WordTrace tailWord_4370482 prefixEnd_4370482 748052652607824900925175 := by
  unfold tailWord_4370482
  simp only [CollatzResearch.WordTrace]
  refine ⟨39851143538124401936316425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106269716101665071830177133 39851143538124401936316425)
  ·
    refine ⟨29888357653593301452237319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39851143538124401936316425 29888357653593301452237319)
    ·
      refine ⟨44832536480389952178355979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29888357653593301452237319 44832536480389952178355979)
      ·
        refine ⟨67248804720584928267533969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44832536480389952178355979 67248804720584928267533969)
        ·
          refine ⟨50436603540438696200650477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67248804720584928267533969 50436603540438696200650477)
          ·
            refine ⟨18913726327664511075243929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50436603540438696200650477 18913726327664511075243929)
            ·
              refine ⟨14185294745748383306432947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18913726327664511075243929 14185294745748383306432947)
              ·
                refine ⟨21277942118622574959649421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14185294745748383306432947 21277942118622574959649421)
                ·
                  refine ⟨7979228294483465609868533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21277942118622574959649421 7979228294483465609868533)
                  ·
                    refine ⟨748052652607824900925175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7979228294483465609868533 748052652607824900925175)
                    ·
                      rfl

theorem cell23_4370482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 3, 5].length) (baseStart_4370482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4370482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4370482 prefixEnd_4370482 := by exact prefixLift 4370482
  have htrace : WordTrace (prefixWord ++ tailWord_4370482) baseStart_4370482 baseEnd_4370482 := by
    simpa [prefixWord, tailWord_4370482, baseEnd_4370482] using wordTrace_append hprefix tailTrace_4370482
  have hstable : (prefixWord ++ tailWord_4370482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4370482).length < 2 ^ (prefixWord ++ tailWord_4370482).sum := by decide
  have hdescent : baseEnd_4370482 < baseStart_4370482 := by decide
  rcases family_descends (prefixWord ++ tailWord_4370482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4370496 : List Nat := [2, 1, 1, 2, 2, 4, 1, 5, 1, 1, 3]
def baseStart_4370496 : Nat := 118140960795 + 4370496 * 2 ^ 59
def prefixEnd_4370496 : Nat := 4983230072969 + 3 ^ 40 * 4370496 * 2
def baseEnd_4370496 : Nat := 2244165146552637648000461

theorem tailTrace_4370496 : CollatzResearch.WordTrace tailWord_4370496 prefixEnd_4370496 2244165146552637648000461 := by
  unfold tailWord_4370496
  simp only [CollatzResearch.WordTrace]
  refine ⟨79702542387223444068137671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106270056516297925424183561 79702542387223444068137671)
  ·
    refine ⟨119553813580835166102206507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79702542387223444068137671 119553813580835166102206507)
    ·
      refine ⟨179330720371252749153309761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119553813580835166102206507 179330720371252749153309761)
      ·
        refine ⟨134498040278439561864982321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179330720371252749153309761 134498040278439561864982321)
        ·
          refine ⟨100873530208829671398736741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134498040278439561864982321 100873530208829671398736741)
          ·
            refine ⟨18913786914155563387263139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 100873530208829671398736741 18913786914155563387263139)
            ·
              refine ⟨28370680371233345080894709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18913786914155563387263139 28370680371233345080894709)
              ·
                refine ⟨2659751284803126101333879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28370680371233345080894709 2659751284803126101333879)
                ·
                  refine ⟨3989626927204689152000819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2659751284803126101333879 3989626927204689152000819)
                  ·
                    refine ⟨5984440390807033728001229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3989626927204689152000819 5984440390807033728001229)
                    ·
                      refine ⟨2244165146552637648000461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5984440390807033728001229 2244165146552637648000461)
                      ·
                        rfl

theorem cell23_4370496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 5, 1, 1, 3].length) (baseStart_4370496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4370496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4370496 prefixEnd_4370496 := by exact prefixLift 4370496
  have htrace : WordTrace (prefixWord ++ tailWord_4370496) baseStart_4370496 baseEnd_4370496 := by
    simpa [prefixWord, tailWord_4370496, baseEnd_4370496] using wordTrace_append hprefix tailTrace_4370496
  have hstable : (prefixWord ++ tailWord_4370496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4370496).length < 2 ^ (prefixWord ++ tailWord_4370496).sum := by decide
  have hdescent : baseEnd_4370496 < baseStart_4370496 := by decide
  rcases family_descends (prefixWord ++ tailWord_4370496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4370522 : List Nat := [3, 1, 1, 2, 1, 1, 5, 2, 1, 1, 5]
def baseStart_4370522 : Nat := 118140960795 + 4370522 * 2 ^ 59
def prefixEnd_4370522 : Nat := 4983230072969 + 3 ^ 40 * 4370522 * 2
def baseEnd_4370522 : Nat := 2244178497049654546275341

theorem tailTrace_4370522 : CollatzResearch.WordTrace tailWord_4370522 prefixEnd_4370522 2244178497049654546275341 := by
  unfold tailWord_4370522
  simp only [CollatzResearch.WordTrace]
  refine ⟨39851508268088173644180455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106270688714901796384481213 39851508268088173644180455)
  ·
    refine ⟨59777262402132260466270683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39851508268088173644180455 59777262402132260466270683)
    ·
      refine ⟨89665893603198390699406025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59777262402132260466270683 89665893603198390699406025)
      ·
        refine ⟨67249420202398793024554519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89665893603198390699406025 67249420202398793024554519)
        ·
          refine ⟨100874130303598189536831779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67249420202398793024554519 100874130303598189536831779)
          ·
            refine ⟨151311195455397284305247669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100874130303598189536831779 151311195455397284305247669)
            ·
              refine ⟨14185424573943495403616969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 151311195455397284305247669 14185424573943495403616969)
              ·
                refine ⟨10639068430457621552712727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14185424573943495403616969 10639068430457621552712727)
                ·
                  refine ⟨15958602645686432329069091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10639068430457621552712727 15958602645686432329069091)
                  ·
                    refine ⟨23937903968529648493603637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15958602645686432329069091 23937903968529648493603637)
                    ·
                      refine ⟨2244178497049654546275341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23937903968529648493603637 2244178497049654546275341)
                      ·
                        rfl

theorem cell23_4370522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 2, 1, 1, 5].length) (baseStart_4370522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4370522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4370522 prefixEnd_4370522 := by exact prefixLift 4370522
  have htrace : WordTrace (prefixWord ++ tailWord_4370522) baseStart_4370522 baseEnd_4370522 := by
    simpa [prefixWord, tailWord_4370522, baseEnd_4370522] using wordTrace_append hprefix tailTrace_4370522
  have hstable : (prefixWord ++ tailWord_4370522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4370522).length < 2 ^ (prefixWord ++ tailWord_4370522).sum := by decide
  have hdescent : baseEnd_4370522 < baseStart_4370522 := by decide
  rcases family_descends (prefixWord ++ tailWord_4370522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4370542 : List Nat := [4, 1, 2, 2, 1, 1, 3, 9]
def baseStart_4370542 : Nat := 118140960795 + 4370542 * 2 ^ 59
def prefixEnd_4370542 : Nat := 4983230072969 + 3 ^ 40 * 4370542 * 2
def baseEnd_4370542 : Nat := 83118102468990535852787

theorem tailTrace_4370542 : CollatzResearch.WordTrace tailWord_4370542 prefixEnd_4370542 83118102468990535852787 := by
  unfold tailWord_4370542
  simp only [CollatzResearch.WordTrace]
  refine ⟨19925845316535029749056235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106271175021520158661633253 19925845316535029749056235)
  ·
    refine ⟨29888767974802544623584353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19925845316535029749056235 29888767974802544623584353)
    ·
      refine ⟨22416575981101908467688265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29888767974802544623584353 22416575981101908467688265)
      ·
        refine ⟨16812431985826431350766199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22416575981101908467688265 16812431985826431350766199)
        ·
          refine ⟨25218647978739647026149299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16812431985826431350766199 25218647978739647026149299)
          ·
            refine ⟨37827971968109470539223949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25218647978739647026149299 37827971968109470539223949)
            ·
              refine ⟨14185489488041051452208981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37827971968109470539223949 14185489488041051452208981)
              ·
                refine ⟨83118102468990535852787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14185489488041051452208981 83118102468990535852787)
                ·
                  rfl

theorem cell23_4370542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 9].length) (baseStart_4370542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4370542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4370542 prefixEnd_4370542 := by exact prefixLift 4370542
  have htrace : WordTrace (prefixWord ++ tailWord_4370542) baseStart_4370542 baseEnd_4370542 := by
    simpa [prefixWord, tailWord_4370542, baseEnd_4370542] using wordTrace_append hprefix tailTrace_4370542
  have hstable : (prefixWord ++ tailWord_4370542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4370542).length < 2 ^ (prefixWord ++ tailWord_4370542).sum := by decide
  have hdescent : baseEnd_4370542 < baseStart_4370542 := by decide
  rcases family_descends (prefixWord ++ tailWord_4370542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4370552 : List Nat := [2, 1, 2, 1, 1, 1, 3, 3, 3, 3, 3]
def baseStart_4370552 : Nat := 118140960795 + 4370552 * 2 ^ 59
def prefixEnd_4370552 : Nat := 4983230072969 + 3 ^ 40 * 4370552 * 2
def baseEnd_4370552 : Nat := 2244193901469289428900203

theorem tailTrace_4370552 : CollatzResearch.WordTrace tailWord_4370552 prefixEnd_4370552 2244193901469289428900203 := by
  unfold tailWord_4370552
  simp only [CollatzResearch.WordTrace]
  refine ⟨79703563631122004850156955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106271418174829339800209273 79703563631122004850156955)
  ·
    refine ⟨119555345446683007275235433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79703563631122004850156955 119555345446683007275235433)
    ·
      refine ⟨89666509085012255456426575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119555345446683007275235433 89666509085012255456426575)
      ·
        refine ⟨134499763627518383184639863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89666509085012255456426575 134499763627518383184639863)
        ·
          refine ⟨201749645441277574776959795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134499763627518383184639863 201749645441277574776959795)
          ·
            refine ⟨302624468161916362165439693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201749645441277574776959795 302624468161916362165439693)
            ·
              refine ⟨113484175560718635812039885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 302624468161916362165439693 113484175560718635812039885)
              ·
                refine ⟨42556565835269488429514957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 113484175560718635812039885 42556565835269488429514957)
                ·
                  refine ⟨15958712188226058161068109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42556565835269488429514957 15958712188226058161068109)
                  ·
                    refine ⟨5984517070584771810400541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15958712188226058161068109 5984517070584771810400541)
                    ·
                      refine ⟨2244193901469289428900203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5984517070584771810400541 2244193901469289428900203)
                      ·
                        rfl

theorem cell23_4370552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 3, 3, 3].length) (baseStart_4370552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4370552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4370552 prefixEnd_4370552 := by exact prefixLift 4370552
  have htrace : WordTrace (prefixWord ++ tailWord_4370552) baseStart_4370552 baseEnd_4370552 := by
    simpa [prefixWord, tailWord_4370552, baseEnd_4370552] using wordTrace_append hprefix tailTrace_4370552
  have hstable : (prefixWord ++ tailWord_4370552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4370552).length < 2 ^ (prefixWord ++ tailWord_4370552).sum := by decide
  have hdescent : baseEnd_4370552 < baseStart_4370552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4370552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4370555 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 3, 9]
def baseStart_4370555 : Nat := 118140960795 + 4370555 * 2 ^ 59
def prefixEnd_4370555 : Nat := 4983230072969 + 3 ^ 40 * 4370555 * 2
def baseEnd_4370555 : Nat := 748065147303750972387563

theorem tailTrace_4370555 : CollatzResearch.WordTrace tailWord_4370555 prefixEnd_4370555 748065147303750972387563 := by
  unfold tailWord_4370555
  simp only [CollatzResearch.WordTrace]
  refine ⟨159407236681233141212673119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106271491120822094141782079 159407236681233141212673119)
  ·
    refine ⟨239110855021849711819009679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159407236681233141212673119 239110855021849711819009679)
    ·
      refine ⟨358666282532774567728514519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239110855021849711819009679 358666282532774567728514519)
      ·
        refine ⟨537999423799161851592771779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 358666282532774567728514519 537999423799161851592771779)
        ·
          refine ⟨806999135698742777389157669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 537999423799161851592771779 806999135698742777389157669)
          ·
            refine ⟨151312337943514270760467063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 806999135698742777389157669 151312337943514270760467063)
            ·
              refine ⟨226968506915271406140700595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151312337943514270760467063 226968506915271406140700595)
              ·
                refine ⟨340452760372907109211050893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 226968506915271406140700595 340452760372907109211050893)
                ·
                  refine ⟨127669785139840165954144085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 340452760372907109211050893 127669785139840165954144085)
                  ·
                    refine ⟨748065147303750972387563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 127669785139840165954144085 748065147303750972387563)
                    ·
                      rfl

theorem cell23_4370555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 9].length) (baseStart_4370555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4370555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4370555 prefixEnd_4370555 := by exact prefixLift 4370555
  have htrace : WordTrace (prefixWord ++ tailWord_4370555) baseStart_4370555 baseEnd_4370555 := by
    simpa [prefixWord, tailWord_4370555, baseEnd_4370555] using wordTrace_append hprefix tailTrace_4370555
  have hstable : (prefixWord ++ tailWord_4370555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4370555).length < 2 ^ (prefixWord ++ tailWord_4370555).sum := by decide
  have hdescent : baseEnd_4370555 < baseStart_4370555 := by decide
  rcases family_descends (prefixWord ++ tailWord_4370555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4370569 : List Nat := [1, 2, 1, 1, 4, 2, 1, 3, 4, 1, 3]
def baseStart_4370569 : Nat := 118140960795 + 4370569 * 2 ^ 59
def prefixEnd_4370569 : Nat := 4983230072969 + 3 ^ 40 * 4370569 * 2
def baseEnd_4370569 : Nat := 2244202630640415862387625

theorem tailTrace_4370569 : CollatzResearch.WordTrace tailWord_4370569 prefixEnd_4370569 2244202630640415862387625 := by
  unfold tailWord_4370569
  simp only [CollatzResearch.WordTrace]
  refine ⟨159407747303182421603682761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106271831535454947735788507 159407747303182421603682761)
  ·
    refine ⟨119555810477386816202762071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159407747303182421603682761 119555810477386816202762071)
    ·
      refine ⟨179333715716080224304143107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119555810477386816202762071 179333715716080224304143107)
      ·
        refine ⟨269000573574120336456214661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179333715716080224304143107 269000573574120336456214661)
        ·
          refine ⟨50437607545147563085540249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 269000573574120336456214661 50437607545147563085540249)
          ·
            refine ⟨37828205658860672314155187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50437607545147563085540249 37828205658860672314155187)
            ·
              refine ⟨56742308488291008471232781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37828205658860672314155187 56742308488291008471232781)
              ·
                refine ⟨21278365683109128176712293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56742308488291008471232781 21278365683109128176712293)
                ·
                  refine ⟨3989693565582961533133555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21278365683109128176712293 3989693565582961533133555)
                  ·
                    refine ⟨5984540348374442299700333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3989693565582961533133555 5984540348374442299700333)
                    ·
                      refine ⟨2244202630640415862387625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5984540348374442299700333 2244202630640415862387625)
                      ·
                        rfl

theorem cell23_4370569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 4, 1, 3].length) (baseStart_4370569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4370569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4370569 prefixEnd_4370569 := by exact prefixLift 4370569
  have htrace : WordTrace (prefixWord ++ tailWord_4370569) baseStart_4370569 baseEnd_4370569 := by
    simpa [prefixWord, tailWord_4370569, baseEnd_4370569] using wordTrace_append hprefix tailTrace_4370569
  have hstable : (prefixWord ++ tailWord_4370569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4370569).length < 2 ^ (prefixWord ++ tailWord_4370569).sum := by decide
  have hdescent : baseEnd_4370569 < baseStart_4370569 := by decide
  rcases family_descends (prefixWord ++ tailWord_4370569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4370579 : List Nat := [1, 1, 1, 2, 1, 2, 3, 4, 3, 3, 2]
def baseStart_4370579 : Nat := 118140960795 + 4370579 * 2 ^ 59
def prefixEnd_4370579 : Nat := 4983230072969 + 3 ^ 40 * 4370579 * 2
def baseEnd_4370579 : Nat := 2244207765446960823262579

theorem tailTrace_4370579 : CollatzResearch.WordTrace tailWord_4370579 prefixEnd_4370579 2244207765446960823262579 := by
  unfold tailWord_4370579
  simp only [CollatzResearch.WordTrace]
  refine ⟨159408112033146193311546791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106272074688764128874364527 159408112033146193311546791)
  ·
    refine ⟨239112168049719289967320187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159408112033146193311546791 239112168049719289967320187)
    ·
      refine ⟨358668252074578934950980281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239112168049719289967320187 358668252074578934950980281)
      ·
        refine ⟨269001189055934201213235211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 358668252074578934950980281 269001189055934201213235211)
        ·
          refine ⟨403501783583901301819852817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 269001189055934201213235211 403501783583901301819852817)
          ·
            refine ⟨302626337687925976364889613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 403501783583901301819852817 302626337687925976364889613)
            ·
              refine ⟨113484876632972241136833605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 302626337687925976364889613 113484876632972241136833605)
              ·
                refine ⟨21278414368682295213156301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 113484876632972241136833605 21278414368682295213156301)
                ·
                  refine ⟨7979405388255860704933613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21278414368682295213156301 7979405388255860704933613)
                  ·
                    refine ⟨2992277020595947764350105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7979405388255860704933613 2992277020595947764350105)
                    ·
                      refine ⟨2244207765446960823262579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2992277020595947764350105 2244207765446960823262579)
                      ·
                        rfl

theorem cell23_4370579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 3, 3, 2].length) (baseStart_4370579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4370579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4370579 prefixEnd_4370579 := by exact prefixLift 4370579
  have htrace : WordTrace (prefixWord ++ tailWord_4370579) baseStart_4370579 baseEnd_4370579 := by
    simpa [prefixWord, tailWord_4370579, baseEnd_4370579] using wordTrace_append hprefix tailTrace_4370579
  have hstable : (prefixWord ++ tailWord_4370579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4370579).length < 2 ^ (prefixWord ++ tailWord_4370579).sum := by decide
  have hdescent : baseEnd_4370579 < baseStart_4370579 := by decide
  rcases family_descends (prefixWord ++ tailWord_4370579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4370590 : List Nat := [4, 3, 1, 1, 3, 2, 1, 2, 1, 2, 3]
def baseStart_4370590 : Nat := 118140960795 + 4370590 * 2 ^ 59
def prefixEnd_4370590 : Nat := 4983230072969 + 3 ^ 40 * 4370590 * 2
def baseEnd_4370590 : Nat := 2244213413734160280225029

theorem tailTrace_4370590 : CollatzResearch.WordTrace tailWord_4370590 prefixEnd_4370590 2244213413734160280225029 := by
  unfold tailWord_4370590
  simp only [CollatzResearch.WordTrace]
  refine ⟨19926064154513292773774653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106272342157404228126798149 19926064154513292773774653)
  ·
    refine ⟨7472274057942484790165495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19926064154513292773774653 7472274057942484790165495)
    ·
      refine ⟨11208411086913727185248243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7472274057942484790165495 11208411086913727185248243)
      ·
        refine ⟨16812616630370590777872365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11208411086913727185248243 16812616630370590777872365)
        ·
          refine ⟨6304731236388971541702137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16812616630370590777872365 6304731236388971541702137)
          ·
            refine ⟨4728548427291728656276603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6304731236388971541702137 4728548427291728656276603)
            ·
              refine ⟨7092822640937592984414905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4728548427291728656276603 7092822640937592984414905)
              ·
                refine ⟨5319616980703194738311179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7092822640937592984414905 5319616980703194738311179)
                ·
                  refine ⟨7979425471054792107466769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5319616980703194738311179 7979425471054792107466769)
                  ·
                    refine ⟨5984569103291094080600077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7979425471054792107466769 5984569103291094080600077)
                    ·
                      refine ⟨2244213413734160280225029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5984569103291094080600077 2244213413734160280225029)
                      ·
                        rfl

theorem cell23_4370590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_4370590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4370590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4370590 prefixEnd_4370590 := by exact prefixLift 4370590
  have htrace : WordTrace (prefixWord ++ tailWord_4370590) baseStart_4370590 baseEnd_4370590 := by
    simpa [prefixWord, tailWord_4370590, baseEnd_4370590] using wordTrace_append hprefix tailTrace_4370590
  have hstable : (prefixWord ++ tailWord_4370590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4370590).length < 2 ^ (prefixWord ++ tailWord_4370590).sum := by decide
  have hdescent : baseEnd_4370590 < baseStart_4370590 := by decide
  rcases family_descends (prefixWord ++ tailWord_4370590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4370632 : List Nat := [2, 1, 3, 1, 2, 1, 1, 5, 7]
def baseStart_4370632 : Nat := 118140960795 + 4370632 * 2 ^ 59
def prefixEnd_4370632 : Nat := 4983230072969 + 3 ^ 40 * 4370632 * 2
def baseEnd_4370632 : Nat := 249359442213516568433315

theorem tailTrace_4370632 : CollatzResearch.WordTrace tailWord_4370632 prefixEnd_4370632 249359442213516568433315 := by
  unfold tailWord_4370632
  simp only [CollatzResearch.WordTrace]
  refine ⟨79705022550977091681613075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106273363401302788908817433 79705022550977091681613075)
  ·
    refine ⟨119557533826465637522419613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79705022550977091681613075 119557533826465637522419613)
    ·
      refine ⟨44834075184924614070907355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119557533826465637522419613 44834075184924614070907355)
      ·
        refine ⟨67251112777386921106361033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44834075184924614070907355 67251112777386921106361033)
        ·
          refine ⟨50438334583040190829770775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67251112777386921106361033 50438334583040190829770775)
          ·
            refine ⟨75657501874560286244656163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50438334583040190829770775 75657501874560286244656163)
            ·
              refine ⟨113486252811840429366984245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75657501874560286244656163 113486252811840429366984245)
              ·
                refine ⟨10639336201110040253154773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 113486252811840429366984245 10639336201110040253154773)
                ·
                  refine ⟨249359442213516568433315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10639336201110040253154773 249359442213516568433315)
                  ·
                    rfl

theorem cell23_4370632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 5, 7].length) (baseStart_4370632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4370632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4370632 prefixEnd_4370632 := by exact prefixLift 4370632
  have htrace : WordTrace (prefixWord ++ tailWord_4370632) baseStart_4370632 baseEnd_4370632 := by
    simpa [prefixWord, tailWord_4370632, baseEnd_4370632] using wordTrace_append hprefix tailTrace_4370632
  have hstable : (prefixWord ++ tailWord_4370632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4370632).length < 2 ^ (prefixWord ++ tailWord_4370632).sum := by decide
  have hdescent : baseEnd_4370632 < baseStart_4370632 := by decide
  rcases family_descends (prefixWord ++ tailWord_4370632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4370636 : List Nat := [2, 2, 1, 6, 1, 1, 1, 1, 2, 6]
def baseStart_4370636 : Nat := 118140960795 + 4370636 * 2 ^ 59
def prefixEnd_4370636 : Nat := 4983230072969 + 3 ^ 40 * 4370636 * 2
def baseEnd_4370636 : Nat := 748079011281422366749939

theorem tailTrace_4370636 : CollatzResearch.WordTrace tailWord_4370636 prefixEnd_4370636 748079011281422366749939 := by
  unfold tailWord_4370636
  simp only [CollatzResearch.WordTrace]
  refine ⟨79705095496969846023185881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106273460662626461364247841 79705095496969846023185881)
  ·
    refine ⟨59778821622727384517389411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79705095496969846023185881 59778821622727384517389411)
    ·
      refine ⟨89668232434091076776084117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59778821622727384517389411 89668232434091076776084117)
      ·
        refine ⟨4203198395348019223878943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 89668232434091076776084117 4203198395348019223878943)
        ·
          refine ⟨6304797593022028835818415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4203198395348019223878943 6304797593022028835818415)
          ·
            refine ⟨9457196389533043253727623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6304797593022028835818415 9457196389533043253727623)
            ·
              refine ⟨14185794584299564880591435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9457196389533043253727623 14185794584299564880591435)
              ·
                refine ⟨21278691876449347320887153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14185794584299564880591435 21278691876449347320887153)
                ·
                  refine ⟨15959018907337010490665365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21278691876449347320887153 15959018907337010490665365)
                  ·
                    refine ⟨748079011281422366749939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15959018907337010490665365 748079011281422366749939)
                    ·
                      rfl

theorem cell23_4370636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 2, 6].length) (baseStart_4370636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4370636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4370636 prefixEnd_4370636 := by exact prefixLift 4370636
  have htrace : WordTrace (prefixWord ++ tailWord_4370636) baseStart_4370636 baseEnd_4370636 := by
    simpa [prefixWord, tailWord_4370636, baseEnd_4370636] using wordTrace_append hprefix tailTrace_4370636
  have hstable : (prefixWord ++ tailWord_4370636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4370636).length < 2 ^ (prefixWord ++ tailWord_4370636).sum := by decide
  have hdescent : baseEnd_4370636 < baseStart_4370636 := by decide
  rcases family_descends (prefixWord ++ tailWord_4370636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4370666 : List Nat := [3, 1, 3, 1, 1, 2, 4, 3, 5]
def baseStart_4370666 : Nat := 118140960795 + 4370666 * 2 ^ 59
def prefixEnd_4370666 : Nat := 4983230072969 + 3 ^ 40 * 4370666 * 2
def baseEnd_4370666 : Nat := 249361382029322442541631

theorem tailTrace_4370666 : CollatzResearch.WordTrace tailWord_4370666 prefixEnd_4370666 249361382029322442541631 := by
  unfold tailWord_4370666
  simp only [CollatzResearch.WordTrace]
  refine ⟨39852821295957751792490963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106274190122554004779975901 39852821295957751792490963)
  ·
    refine ⟨59779231943936627688736445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39852821295957751792490963 59779231943936627688736445)
    ·
      refine ⟨22417211978976235383276167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59779231943936627688736445 22417211978976235383276167)
      ·
        refine ⟨33625817968464353074914251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22417211978976235383276167 33625817968464353074914251)
        ·
          refine ⟨50438726952696529612371377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33625817968464353074914251 50438726952696529612371377)
          ·
            refine ⟨37829045214522397209278533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50438726952696529612371377 37829045214522397209278533)
            ·
              refine ⟨7092945977722949476739725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37829045214522397209278533 7092945977722949476739725)
              ·
                refine ⟨2659854741646106053777397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7092945977722949476739725 2659854741646106053777397)
                ·
                  refine ⟨249361382029322442541631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2659854741646106053777397 249361382029322442541631)
                  ·
                    rfl

theorem cell23_4370666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 3, 5].length) (baseStart_4370666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4370666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4370666 prefixEnd_4370666 := by exact prefixLift 4370666
  have htrace : WordTrace (prefixWord ++ tailWord_4370666) baseStart_4370666 baseEnd_4370666 := by
    simpa [prefixWord, tailWord_4370666, baseEnd_4370666] using wordTrace_append hprefix tailTrace_4370666
  have hstable : (prefixWord ++ tailWord_4370666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4370666).length < 2 ^ (prefixWord ++ tailWord_4370666).sum := by decide
  have hdescent : baseEnd_4370666 < baseStart_4370666 := by decide
  rcases family_descends (prefixWord ++ tailWord_4370666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4370672 : List Nat := [2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 5]
def baseStart_4370672 : Nat := 118140960795 + 4370672 * 2 ^ 59
def prefixEnd_4370672 : Nat := 4983230072969 + 3 ^ 40 * 4370672 * 2
def baseEnd_4370672 : Nat := 2244255519147828959399651

theorem tailTrace_4370672 : CollatzResearch.WordTrace tailWord_4370672 prefixEnd_4370672 2244255519147828959399651 := by
  unfold tailWord_4370672
  simp only [CollatzResearch.WordTrace]
  refine ⟨79705752010904635097341135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106274336014539513463121513 79705752010904635097341135)
  ·
    refine ⟨119558628016356952646011703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79705752010904635097341135 119558628016356952646011703)
    ·
      refine ⟨179337942024535428969017555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119558628016356952646011703 179337942024535428969017555)
      ·
        refine ⟨269006913036803143453526333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179337942024535428969017555 269006913036803143453526333)
        ·
          refine ⟨100877592388801178795072375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 269006913036803143453526333 100877592388801178795072375)
          ·
            refine ⟨151316388583201768192608563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100877592388801178795072375 151316388583201768192608563)
            ·
              refine ⟨226974582874802652288912845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151316388583201768192608563 226974582874802652288912845)
              ·
                refine ⟨85115468578050994608342317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 226974582874802652288912845 85115468578050994608342317)
                ·
                  refine ⟨31918300716769122978128369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 85115468578050994608342317 31918300716769122978128369)
                  ·
                    refine ⟨23938725537576842233596277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31918300716769122978128369 23938725537576842233596277)
                    ·
                      refine ⟨2244255519147828959399651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23938725537576842233596277 2244255519147828959399651)
                      ·
                        rfl

theorem cell23_4370672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 5].length) (baseStart_4370672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4370672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4370672 prefixEnd_4370672 := by exact prefixLift 4370672
  have htrace : WordTrace (prefixWord ++ tailWord_4370672) baseStart_4370672 baseEnd_4370672 := by
    simpa [prefixWord, tailWord_4370672, baseEnd_4370672] using wordTrace_append hprefix tailTrace_4370672
  have hstable : (prefixWord ++ tailWord_4370672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4370672).length < 2 ^ (prefixWord ++ tailWord_4370672).sum := by decide
  have hdescent : baseEnd_4370672 < baseStart_4370672 := by decide
  rcases family_descends (prefixWord ++ tailWord_4370672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4370739 : List Nat := [1, 1, 1, 2, 5, 1, 2, 4, 6]
def baseStart_4370739 : Nat := 118140960795 + 4370739 * 2 ^ 59
def prefixEnd_4370739 : Nat := 4983230072969 + 3 ^ 40 * 4370739 * 2
def baseEnd_4370739 : Nat := 249365546927964466362427

theorem tailTrace_4370739 : CollatzResearch.WordTrace tailWord_4370739 prefixEnd_4370739 249365546927964466362427 := by
  unfold tailWord_4370739
  simp only [CollatzResearch.WordTrace]
  refine ⟨159413947712566540637371271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106275965141711027091580847 159413947712566540637371271)
  ·
    refine ⟨239120921568849810956056907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159413947712566540637371271 239120921568849810956056907)
    ·
      refine ⟨358681382353274716434085361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239120921568849810956056907 358681382353274716434085361)
      ·
        refine ⟨269011036764956037325564021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 358681382353274716434085361 269011036764956037325564021)
        ·
          refine ⟨25219784696714628499271627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 269011036764956037325564021 25219784696714628499271627)
          ·
            refine ⟨37829677045071942748907441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25219784696714628499271627 37829677045071942748907441)
            ·
              refine ⟨28372257783803957061680581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37829677045071942748907441 28372257783803957061680581)
              ·
                refine ⟨5319798334463241949065109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28372257783803957061680581 5319798334463241949065109)
                ·
                  refine ⟨249365546927964466362427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5319798334463241949065109 249365546927964466362427)
                  ·
                    rfl

theorem cell23_4370739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 4, 6].length) (baseStart_4370739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4370739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4370739 prefixEnd_4370739 := by exact prefixLift 4370739
  have htrace : WordTrace (prefixWord ++ tailWord_4370739) baseStart_4370739 baseEnd_4370739 := by
    simpa [prefixWord, tailWord_4370739, baseEnd_4370739] using wordTrace_append hprefix tailTrace_4370739
  have hstable : (prefixWord ++ tailWord_4370739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4370739).length < 2 ^ (prefixWord ++ tailWord_4370739).sum := by decide
  have hdescent : baseEnd_4370739 < baseStart_4370739 := by decide
  rcases family_descends (prefixWord ++ tailWord_4370739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4370800 : List Nat := [2, 1, 1, 1, 4, 4, 1, 4, 1, 1, 3]
def baseStart_4370800 : Nat := 118140960795 + 4370800 * 2 ^ 59
def prefixEnd_4370800 : Nat := 4983230072969 + 3 ^ 40 * 4370800 * 2
def baseEnd_4370800 : Nat := 2244321244671604458599063

theorem tailTrace_4370800 : CollatzResearch.WordTrace tailWord_4370800 prefixEnd_4370800 2244321244671604458599063 := by
  unfold tailWord_4370800
  simp only [CollatzResearch.WordTrace]
  refine ⟨79708086282672774027670927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106277448376897032036894569 79708086282672774027670927)
  ·
    refine ⟨119562129424009161041506391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79708086282672774027670927 119562129424009161041506391)
    ·
      refine ⟨179343194136013741562259587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119562129424009161041506391 179343194136013741562259587)
      ·
        refine ⟨269014791204020612343389381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179343194136013741562259587 269014791204020612343389381)
        ·
          refine ⟨50440273350753864814385509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 269014791204020612343389381 50440273350753864814385509)
          ·
            refine ⟨9457551253266349652697283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50440273350753864814385509 9457551253266349652697283)
            ·
              refine ⟨14186326879899524479045925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9457551253266349652697283 14186326879899524479045925)
              ·
                refine ⟨2659936289981160839821111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14186326879899524479045925 2659936289981160839821111)
                ·
                  refine ⟨3989904434971741259731667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2659936289981160839821111 3989904434971741259731667)
                  ·
                    refine ⟨5984856652457611889597501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3989904434971741259731667 5984856652457611889597501)
                    ·
                      refine ⟨2244321244671604458599063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5984856652457611889597501 2244321244671604458599063)
                      ·
                        rfl

theorem cell23_4370800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 4, 1, 1, 3].length) (baseStart_4370800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4370800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4370800 prefixEnd_4370800 := by exact prefixLift 4370800
  have htrace : WordTrace (prefixWord ++ tailWord_4370800) baseStart_4370800 baseEnd_4370800 := by
    simpa [prefixWord, tailWord_4370800, baseEnd_4370800] using wordTrace_append hprefix tailTrace_4370800
  have hstable : (prefixWord ++ tailWord_4370800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4370800).length < 2 ^ (prefixWord ++ tailWord_4370800).sum := by decide
  have hdescent : baseEnd_4370800 < baseStart_4370800 := by decide
  rcases family_descends (prefixWord ++ tailWord_4370800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4370809 : List Nat := [1, 2, 1, 3, 2, 1, 1, 3, 3, 1, 5]
def baseStart_4370809 : Nat := 118140960795 + 4370809 * 2 ^ 59
def prefixEnd_4370809 : Nat := 4983230072969 + 3 ^ 40 * 4370809 * 2
def baseEnd_4370809 : Nat := 2244325865997494923386521

theorem tailTrace_4370809 : CollatzResearch.WordTrace tailWord_4370809 prefixEnd_4370809 2244325865997494923386521 := by
  unfold tailWord_4370809
  simp only [CollatzResearch.WordTrace]
  refine ⟨159416500822312942592419481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106277667214875295061612987 159416500822312942592419481)
  ·
    refine ⟨119562375616734706944314611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159416500822312942592419481 119562375616734706944314611)
    ·
      refine ⟨179343563425102060416471917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119562375616734706944314611 179343563425102060416471917)
      ·
        refine ⟨67253836284413272656176969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 179343563425102060416471917 67253836284413272656176969)
        ·
          refine ⟨50440377213309954492132727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67253836284413272656176969 50440377213309954492132727)
          ·
            refine ⟨75660565819964931738199091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50440377213309954492132727 75660565819964931738199091)
            ·
              refine ⟨113490848729947397607298637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75660565819964931738199091 113490848729947397607298637)
              ·
                refine ⟨42559068273730274102736989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 113490848729947397607298637 42559068273730274102736989)
                ·
                  refine ⟨15959650602648852788526371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42559068273730274102736989 15959650602648852788526371)
                  ·
                    refine ⟨23939475903973279182789557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15959650602648852788526371 23939475903973279182789557)
                    ·
                      refine ⟨2244325865997494923386521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23939475903973279182789557 2244325865997494923386521)
                      ·
                        rfl

theorem cell23_4370809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 3, 1, 5].length) (baseStart_4370809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4370809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4370809 prefixEnd_4370809 := by exact prefixLift 4370809
  have htrace : WordTrace (prefixWord ++ tailWord_4370809) baseStart_4370809 baseEnd_4370809 := by
    simpa [prefixWord, tailWord_4370809, baseEnd_4370809] using wordTrace_append hprefix tailTrace_4370809
  have hstable : (prefixWord ++ tailWord_4370809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4370809).length < 2 ^ (prefixWord ++ tailWord_4370809).sum := by decide
  have hdescent : baseEnd_4370809 < baseStart_4370809 := by decide
  rcases family_descends (prefixWord ++ tailWord_4370809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4370840 : List Nat := [2, 1, 2, 5, 1, 1, 4, 1, 1, 1, 4]
def baseStart_4370840 : Nat := 118140960795 + 4370840 * 2 ^ 59
def prefixEnd_4370840 : Nat := 4983230072969 + 3 ^ 40 * 4370840 * 2
def baseEnd_4370840 : Nat := 2244341783897784302098879

theorem tailTrace_4370840 : CollatzResearch.WordTrace tailWord_4370840 prefixEnd_4370840 2244341783897784302098879 := by
  unfold tailWord_4370840
  simp only [CollatzResearch.WordTrace]
  refine ⟨79708815742600317443398987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106278420990133756591198649 79708815742600317443398987)
  ·
    refine ⟨119563223613900476165098481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79708815742600317443398987 119563223613900476165098481)
    ·
      refine ⟨89672417710425357123823861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119563223613900476165098481 89672417710425357123823861)
      ·
        refine ⟨8406789160352377230358487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 89672417710425357123823861 8406789160352377230358487)
        ·
          refine ⟨12610183740528565845537731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8406789160352377230358487 12610183740528565845537731)
          ·
            refine ⟨18915275610792848768306597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12610183740528565845537731 18915275610792848768306597)
            ·
              refine ⟨3546614177023659144057487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18915275610792848768306597 3546614177023659144057487)
              ·
                refine ⟨5319921265535488716086231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3546614177023659144057487 5319921265535488716086231)
                ·
                  refine ⟨7979881898303233074129347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5319921265535488716086231 7979881898303233074129347)
                  ·
                    refine ⟨11969822847454849611194021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7979881898303233074129347 11969822847454849611194021)
                    ·
                      refine ⟨2244341783897784302098879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11969822847454849611194021 2244341783897784302098879)
                      ·
                        rfl

theorem cell23_4370840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_4370840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4370840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4370840 prefixEnd_4370840 := by exact prefixLift 4370840
  have htrace : WordTrace (prefixWord ++ tailWord_4370840) baseStart_4370840 baseEnd_4370840 := by
    simpa [prefixWord, tailWord_4370840, baseEnd_4370840] using wordTrace_append hprefix tailTrace_4370840
  have hstable : (prefixWord ++ tailWord_4370840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4370840).length < 2 ^ (prefixWord ++ tailWord_4370840).sum := by decide
  have hdescent : baseEnd_4370840 < baseStart_4370840 := by decide
  rcases family_descends (prefixWord ++ tailWord_4370840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4370873 : List Nat := [1, 2, 1, 4, 3, 1, 3, 1, 1, 3, 3]
def baseStart_4370873 : Nat := 118140960795 + 4370873 * 2 ^ 59
def prefixEnd_4370873 : Nat := 4983230072969 + 3 ^ 40 * 4370873 * 2
def baseEnd_4370873 : Nat := 2244358728759382672986227

theorem tailTrace_4370873 : CollatzResearch.WordTrace tailWord_4370873 prefixEnd_4370873 2244358728759382672986227 := by
  unfold tailWord_4370873
  simp only [CollatzResearch.WordTrace]
  refine ⟨159418835094081081522749273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106279223396054054348499515 159418835094081081522749273)
  ·
    refine ⟨119564126320560811142061955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159418835094081081522749273 119564126320560811142061955)
    ·
      refine ⟨179346189480841216713092933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119564126320560811142061955 179346189480841216713092933)
      ·
        refine ⟨33627410527657728133704925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 179346189480841216713092933 33627410527657728133704925)
        ·
          refine ⟨12610278947871648050139347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33627410527657728133704925 12610278947871648050139347)
          ·
            refine ⟨18915418421807472075209021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12610278947871648050139347 18915418421807472075209021)
            ·
              refine ⟨7093281908177802028203383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18915418421807472075209021 7093281908177802028203383)
              ·
                refine ⟨10639922862266703042305075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7093281908177802028203383 10639922862266703042305075)
                ·
                  refine ⟨15959884293400054563457613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10639922862266703042305075 15959884293400054563457613)
                  ·
                    refine ⟨5984956610025020461296605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15959884293400054563457613 5984956610025020461296605)
                    ·
                      refine ⟨2244358728759382672986227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5984956610025020461296605 2244358728759382672986227)
                      ·
                        rfl

theorem cell23_4370873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 1, 1, 3, 3].length) (baseStart_4370873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4370873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4370873 prefixEnd_4370873 := by exact prefixLift 4370873
  have htrace : WordTrace (prefixWord ++ tailWord_4370873) baseStart_4370873 baseEnd_4370873 := by
    simpa [prefixWord, tailWord_4370873, baseEnd_4370873] using wordTrace_append hprefix tailTrace_4370873
  have hstable : (prefixWord ++ tailWord_4370873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4370873).length < 2 ^ (prefixWord ++ tailWord_4370873).sum := by decide
  have hdescent : baseEnd_4370873 < baseStart_4370873 := by decide
  rcases family_descends (prefixWord ++ tailWord_4370873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4370889 : List Nat := [1, 2, 1, 1, 2, 1, 4, 2, 1, 8]
def baseStart_4370889 : Nat := 118140960795 + 4370889 * 2 ^ 59
def prefixEnd_4370889 : Nat := 4983230072969 + 3 ^ 40 * 4370889 * 2
def baseEnd_4370889 : Nat := 748122314816618203462051

theorem tailTrace_4370889 : CollatzResearch.WordTrace tailWord_4370889 prefixEnd_4370889 748122314816618203462051 := by
  unfold tailWord_4370889
  simp only [CollatzResearch.WordTrace]
  refine ⟨159419418662023116255331721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106279612441348744170221147 159419418662023116255331721)
  ·
    refine ⟨119564563996517337191498791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159419418662023116255331721 119564563996517337191498791)
    ·
      refine ⟨179346845994776005787248187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119564563996517337191498791 179346845994776005787248187)
      ·
        refine ⟨269020268992164008680872281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179346845994776005787248187 269020268992164008680872281)
        ·
          refine ⟨201765201744123006510654211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 269020268992164008680872281 201765201744123006510654211)
          ·
            refine ⟨302647802616184509765981317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201765201744123006510654211 302647802616184509765981317)
            ·
              refine ⟨56746462990534595581121497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 302647802616184509765981317 56746462990534595581121497)
              ·
                refine ⟨42559847242900946685841123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56746462990534595581121497 42559847242900946685841123)
                ·
                  refine ⟨63839770864351420028761685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42559847242900946685841123 63839770864351420028761685)
                  ·
                    refine ⟨748122314816618203462051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 63839770864351420028761685 748122314816618203462051)
                    ·
                      rfl

theorem cell23_4370889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 8].length) (baseStart_4370889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4370889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4370889 prefixEnd_4370889 := by exact prefixLift 4370889
  have htrace : WordTrace (prefixWord ++ tailWord_4370889) baseStart_4370889 baseEnd_4370889 := by
    simpa [prefixWord, tailWord_4370889, baseEnd_4370889] using wordTrace_append hprefix tailTrace_4370889
  have hstable : (prefixWord ++ tailWord_4370889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4370889).length < 2 ^ (prefixWord ++ tailWord_4370889).sum := by decide
  have hdescent : baseEnd_4370889 < baseStart_4370889 := by decide
  rcases family_descends (prefixWord ++ tailWord_4370889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4370964 : List Nat := [2, 4, 3, 1, 1, 1, 1, 4, 2, 2, 2]
def baseStart_4370964 : Nat := 118140960795 + 4370964 * 2 ^ 59
def prefixEnd_4370964 : Nat := 4983230072969 + 3 ^ 40 * 4370964 * 2
def baseEnd_4370964 : Nat := 2244405455498941816948309

theorem tailTrace_4370964 : CollatzResearch.WordTrace tailWord_4370964 prefixEnd_4370964 2244405455498941816948309 := by
  unfold tailWord_4370964
  simp only [CollatzResearch.WordTrace]
  refine ⟨79711077068375702032155973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106281436091167602709541297 79711077068375702032155973)
  ·
    refine ⟨14945826950320444131029245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79711077068375702032155973 14945826950320444131029245)
    ·
      refine ⟨5604685106370166549135967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14945826950320444131029245 5604685106370166549135967)
      ·
        refine ⟨8407027659555249823703951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5604685106370166549135967 8407027659555249823703951)
        ·
          refine ⟨12610541489332874735555927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8407027659555249823703951 12610541489332874735555927)
          ·
            refine ⟨18915812233999312103333891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12610541489332874735555927 18915812233999312103333891)
            ·
              refine ⟨28373718350998968155000837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18915812233999312103333891 28373718350998968155000837)
              ·
                refine ⟨5320072190812306529062657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28373718350998968155000837 5320072190812306529062657)
                ·
                  refine ⟨3990054143109229896796993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5320072190812306529062657 3990054143109229896796993)
                  ·
                    refine ⟨2992540607331922422597745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3990054143109229896796993 2992540607331922422597745)
                    ·
                      refine ⟨2244405455498941816948309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2992540607331922422597745 2244405455498941816948309)
                      ·
                        rfl

theorem cell23_4370964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_4370964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4370964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4370964 prefixEnd_4370964 := by exact prefixLift 4370964
  have htrace : WordTrace (prefixWord ++ tailWord_4370964) baseStart_4370964 baseEnd_4370964 := by
    simpa [prefixWord, tailWord_4370964, baseEnd_4370964] using wordTrace_append hprefix tailTrace_4370964
  have hstable : (prefixWord ++ tailWord_4370964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4370964).length < 2 ^ (prefixWord ++ tailWord_4370964).sum := by decide
  have hdescent : baseEnd_4370964 < baseStart_4370964 := by decide
  rcases family_descends (prefixWord ++ tailWord_4370964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4370970 : List Nat := [3, 1, 1, 3, 1, 1, 6, 2, 5]
def baseStart_4370970 : Nat := 118140960795 + 4370970 * 2 ^ 59
def prefixEnd_4370970 : Nat := 4983230072969 + 3 ^ 40 * 4370970 * 2
def baseEnd_4370970 : Nat := 249378726264763199274809

theorem tailTrace_4370970 : CollatzResearch.WordTrace tailWord_4370970 prefixEnd_4370970 249378726264763199274809 := by
  unfold tailWord_4370970
  simp only [CollatzResearch.WordTrace]
  refine ⟨39855593243682416772257591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106281581983153111392686909 39855593243682416772257591)
  ·
    refine ⟨59783389865523625158386387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39855593243682416772257591 59783389865523625158386387)
    ·
      refine ⟨89675084798285437737579581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59783389865523625158386387 89675084798285437737579581)
      ·
        refine ⟨33628156799357039151592343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89675084798285437737579581 33628156799357039151592343)
        ·
          refine ⟨50442235199035558727388515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33628156799357039151592343 50442235199035558727388515)
          ·
            refine ⟨75663352798553338091082773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50442235199035558727388515 75663352798553338091082773)
            ·
              refine ⟨3546719662432187723019505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 75663352798553338091082773 3546719662432187723019505)
              ·
                refine ⟨2660039746824140792264629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3546719662432187723019505 2660039746824140792264629)
                ·
                  refine ⟨249378726264763199274809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2660039746824140792264629 249378726264763199274809)
                  ·
                    rfl

theorem cell23_4370970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 6, 2, 5].length) (baseStart_4370970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4370970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4370970 prefixEnd_4370970 := by exact prefixLift 4370970
  have htrace : WordTrace (prefixWord ++ tailWord_4370970) baseStart_4370970 baseEnd_4370970 := by
    simpa [prefixWord, tailWord_4370970, baseEnd_4370970] using wordTrace_append hprefix tailTrace_4370970
  have hstable : (prefixWord ++ tailWord_4370970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4370970).length < 2 ^ (prefixWord ++ tailWord_4370970).sum := by decide
  have hdescent : baseEnd_4370970 < baseStart_4370970 := by decide
  rcases family_descends (prefixWord ++ tailWord_4370970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4371016 : List Nat := [2, 1, 3, 1, 1, 1, 1, 2, 1, 6, 4]
def baseStart_4371016 : Nat := 118140960795 + 4371016 * 2 ^ 59
def prefixEnd_4371016 : Nat := 4983230072969 + 3 ^ 40 * 4371016 * 2
def baseEnd_4371016 : Nat := 2244432156492975613498069

theorem tailTrace_4371016 : CollatzResearch.WordTrace tailWord_4371016 prefixEnd_4371016 2244432156492975613498069 := by
  unfold tailWord_4371016
  simp only [CollatzResearch.WordTrace]
  refine ⟨79712025366281508472602451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106282700488375344630136601 79712025366281508472602451)
  ·
    refine ⟨119568038049422262708903677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79712025366281508472602451 119568038049422262708903677)
    ·
      refine ⟨44838014268533348515838879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119568038049422262708903677 44838014268533348515838879)
      ·
        refine ⟨67257021402800022773758319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44838014268533348515838879 67257021402800022773758319)
        ·
          refine ⟨100885532104200034160637479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67257021402800022773758319 100885532104200034160637479)
          ·
            refine ⟨151328298156300051240956219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100885532104200034160637479 151328298156300051240956219)
            ·
              refine ⟨226992447234450076861434329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151328298156300051240956219 226992447234450076861434329)
              ·
                refine ⟨170244335425837557646075747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 226992447234450076861434329 170244335425837557646075747)
                ·
                  refine ⟨255366503138756336469113621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 170244335425837557646075747 255366503138756336469113621)
                  ·
                    refine ⟨11970304834629203271989701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 255366503138756336469113621 11970304834629203271989701)
                    ·
                      refine ⟨2244432156492975613498069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11970304834629203271989701 2244432156492975613498069)
                      ·
                        rfl

theorem cell23_4371016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 1, 6, 4].length) (baseStart_4371016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4371016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4371016 prefixEnd_4371016 := by exact prefixLift 4371016
  have htrace : WordTrace (prefixWord ++ tailWord_4371016) baseStart_4371016 baseEnd_4371016 := by
    simpa [prefixWord, tailWord_4371016, baseEnd_4371016] using wordTrace_append hprefix tailTrace_4371016
  have hstable : (prefixWord ++ tailWord_4371016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4371016).length < 2 ^ (prefixWord ++ tailWord_4371016).sum := by decide
  have hdescent : baseEnd_4371016 < baseStart_4371016 := by decide
  rcases family_descends (prefixWord ++ tailWord_4371016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4371023 : List Nat := [1, 1, 2, 1, 1, 2, 4, 4, 2, 2, 3]
def baseStart_4371023 : Nat := 118140960795 + 4371023 * 2 ^ 59
def prefixEnd_4371023 : Nat := 4983230072969 + 3 ^ 40 * 4371023 * 2
def baseEnd_4371023 : Nat := 2244435750857557086110537

theorem tailTrace_4371023 : CollatzResearch.WordTrace tailWord_4371023 prefixEnd_4371023 2244435750857557086110537 := by
  unfold tailWord_4371023
  simp only [CollatzResearch.WordTrace]
  refine ⟨159424306043537657140709723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106282870695691771427139815 159424306043537657140709723)
  ·
    refine ⟨239136459065306485711064585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159424306043537657140709723 239136459065306485711064585)
    ·
      refine ⟨179352344298979864283298439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 239136459065306485711064585 179352344298979864283298439)
      ·
        refine ⟨269028516448469796424947659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179352344298979864283298439 269028516448469796424947659)
        ·
          refine ⟨403542774672704694637421489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 269028516448469796424947659 403542774672704694637421489)
          ·
            refine ⟨302657081004528520978066117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 403542774672704694637421489 302657081004528520978066117)
            ·
              refine ⟨56748202688349097683387397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 302657081004528520978066117 56748202688349097683387397)
              ·
                refine ⟨10640288004065455815635137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56748202688349097683387397 10640288004065455815635137)
                ·
                  refine ⟨7980216003049091861726353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10640288004065455815635137 7980216003049091861726353)
                  ·
                    refine ⟨5985162002286818896294765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7980216003049091861726353 5985162002286818896294765)
                    ·
                      refine ⟨2244435750857557086110537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5985162002286818896294765 2244435750857557086110537)
                      ·
                        rfl

theorem cell23_4371023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 4, 2, 2, 3].length) (baseStart_4371023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4371023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4371023 prefixEnd_4371023 := by exact prefixLift 4371023
  have htrace : WordTrace (prefixWord ++ tailWord_4371023) baseStart_4371023 baseEnd_4371023 := by
    simpa [prefixWord, tailWord_4371023, baseEnd_4371023] using wordTrace_append hprefix tailTrace_4371023
  have hstable : (prefixWord ++ tailWord_4371023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4371023).length < 2 ^ (prefixWord ++ tailWord_4371023).sum := by decide
  have hdescent : baseEnd_4371023 < baseStart_4371023 := by decide
  rcases family_descends (prefixWord ++ tailWord_4371023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4371066 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 4, 1, 7]
def baseStart_4371066 : Nat := 118140960795 + 4371066 * 2 ^ 59
def prefixEnd_4371066 : Nat := 4983230072969 + 3 ^ 40 * 4371066 * 2
def baseEnd_4371066 : Nat := 2244457830525700417872839

theorem tailTrace_4371066 : CollatzResearch.WordTrace tailWord_4371066 prefixEnd_4371066 2244457830525700417872839 := by
  unfold tailWord_4371066
  simp only [CollatzResearch.WordTrace]
  refine ⟨39856468595595468871131263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106283916254921250323016701 39856468595595468871131263)
  ·
    refine ⟨59784702893393203306696895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39856468595595468871131263 59784702893393203306696895)
    ·
      refine ⟨89677054340089804960045343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59784702893393203306696895 89677054340089804960045343)
      ·
        refine ⟨134515581510134707440068015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89677054340089804960045343 134515581510134707440068015)
        ·
          refine ⟨201773372265202061160102023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134515581510134707440068015 201773372265202061160102023)
          ·
            refine ⟨302660058397803091740153035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201773372265202061160102023 302660058397803091740153035)
            ·
              refine ⟨453990087596704637610229553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 302660058397803091740153035 453990087596704637610229553)
              ·
                refine ⟨340492565697528478207672165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 453990087596704637610229553 340492565697528478207672165)
                ·
                  refine ⟨63842356068286589663938531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 340492565697528478207672165 63842356068286589663938531)
                  ·
                    refine ⟨95763534102429884495907797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 63842356068286589663938531 95763534102429884495907797)
                    ·
                      refine ⟨2244457830525700417872839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 95763534102429884495907797 2244457830525700417872839)
                      ·
                        rfl

theorem cell23_4371066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 4, 1, 7].length) (baseStart_4371066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4371066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4371066 prefixEnd_4371066 := by exact prefixLift 4371066
  have htrace : WordTrace (prefixWord ++ tailWord_4371066) baseStart_4371066 baseEnd_4371066 := by
    simpa [prefixWord, tailWord_4371066, baseEnd_4371066] using wordTrace_append hprefix tailTrace_4371066
  have hstable : (prefixWord ++ tailWord_4371066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4371066).length < 2 ^ (prefixWord ++ tailWord_4371066).sum := by decide
  have hdescent : baseEnd_4371066 < baseStart_4371066 := by decide
  rcases family_descends (prefixWord ++ tailWord_4371066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4371123 : List Nat := [1, 1, 1, 2, 3, 4, 1, 1, 3, 2, 4]
def baseStart_4371123 : Nat := 118140960795 + 4371123 * 2 ^ 59
def prefixEnd_4371123 : Nat := 4983230072969 + 3 ^ 40 * 4371123 * 2
def baseEnd_4371123 : Nat := 2244487098923006694860077

theorem tailTrace_4371123 : CollatzResearch.WordTrace tailWord_4371123 prefixEnd_4371123 2244487098923006694860077 := by
  unfold tailWord_4371123
  simp only [CollatzResearch.WordTrace]
  refine ⟨159427953343175374219350023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106285302228783582812900015 159427953343175374219350023)
  ·
    refine ⟨239141930014763061329025035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159427953343175374219350023 239141930014763061329025035)
    ·
      refine ⟨358712895022144591993537553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239141930014763061329025035 358712895022144591993537553)
      ·
        refine ⟨269034671266608443995153165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 358712895022144591993537553 269034671266608443995153165)
        ·
          refine ⟨100888001724978166498182437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 269034671266608443995153165 100888001724978166498182437)
          ·
            refine ⟨18916500323433406218409207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 100888001724978166498182437 18916500323433406218409207)
            ·
              refine ⟨28374750485150109327613811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18916500323433406218409207 28374750485150109327613811)
              ·
                refine ⟨42562125727725163991420717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28374750485150109327613811 42562125727725163991420717)
                ·
                  refine ⟨15960797147896936496782769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42562125727725163991420717 15960797147896936496782769)
                  ·
                    refine ⟨11970597860922702372587077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15960797147896936496782769 11970597860922702372587077)
                    ·
                      refine ⟨2244487098923006694860077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11970597860922702372587077 2244487098923006694860077)
                      ·
                        rfl

theorem cell23_4371123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 3, 2, 4].length) (baseStart_4371123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4371123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4371123 prefixEnd_4371123 := by exact prefixLift 4371123
  have htrace : WordTrace (prefixWord ++ tailWord_4371123) baseStart_4371123 baseEnd_4371123 := by
    simpa [prefixWord, tailWord_4371123, baseEnd_4371123] using wordTrace_append hprefix tailTrace_4371123
  have hstable : (prefixWord ++ tailWord_4371123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4371123).length < 2 ^ (prefixWord ++ tailWord_4371123).sum := by decide
  have hdescent : baseEnd_4371123 < baseStart_4371123 := by decide
  rcases family_descends (prefixWord ++ tailWord_4371123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4371150 : List Nat := [4, 1, 1, 1, 3, 4, 1, 8]
def baseStart_4371150 : Nat := 118140960795 + 4371150 * 2 ^ 59
def prefixEnd_4371150 : Nat := 4983230072969 + 3 ^ 40 * 4371150 * 2
def baseEnd_4371150 : Nat := 83129665292617707008239

theorem tailTrace_4371150 : CollatzResearch.WordTrace tailWord_4371150 prefixEnd_4371150 83129665292617707008239 := by
  unfold tailWord_4371150
  simp only [CollatzResearch.WordTrace]
  refine ⟨19928617264259694728822863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106285958742718371887055269 19928617264259694728822863)
  ·
    refine ⟨29892925896389542093234295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19928617264259694728822863 29892925896389542093234295)
    ·
      refine ⟨44839388844584313139851443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29892925896389542093234295 44839388844584313139851443)
      ·
        refine ⟨67259083266876469709777165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44839388844584313139851443 67259083266876469709777165)
        ·
          refine ⟨25222156225078676141166437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67259083266876469709777165 25222156225078676141166437)
          ·
            refine ⟨4729154292202251776468707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25222156225078676141166437 4729154292202251776468707)
            ·
              refine ⟨7093731438303377664703061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4729154292202251776468707 7093731438303377664703061)
              ·
                refine ⟨83129665292617707008239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7093731438303377664703061 83129665292617707008239)
                ·
                  rfl

theorem cell23_4371150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 8].length) (baseStart_4371150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4371150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4371150 prefixEnd_4371150 := by exact prefixLift 4371150
  have htrace : WordTrace (prefixWord ++ tailWord_4371150) baseStart_4371150 baseEnd_4371150 := by
    simpa [prefixWord, tailWord_4371150, baseEnd_4371150] using wordTrace_append hprefix tailTrace_4371150
  have hstable : (prefixWord ++ tailWord_4371150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4371150).length < 2 ^ (prefixWord ++ tailWord_4371150).sum := by decide
  have hdescent : baseEnd_4371150 < baseStart_4371150 := by decide
  rcases family_descends (prefixWord ++ tailWord_4371150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4371160 : List Nat := [2, 1, 2, 2, 3, 2, 1, 3, 1, 3, 3]
def baseStart_4371160 : Nat := 118140960795 + 4371160 * 2 ^ 59
def prefixEnd_4371160 : Nat := 4983230072969 + 3 ^ 40 * 4371160 * 2
def baseEnd_4371160 : Nat := 2244506097707223050097407

theorem tailTrace_4371160 : CollatzResearch.WordTrace tailWord_4371160 prefixEnd_4371160 2244506097707223050097407 := by
  unfold tailWord_4371160
  simp only [CollatzResearch.WordTrace]
  refine ⟨79714651422020664769223467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106286201896027553025631289 79714651422020664769223467)
  ·
    refine ⟨119571977133030997153835201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79714651422020664769223467 119571977133030997153835201)
    ·
      refine ⟨89678982849773247865376401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119571977133030997153835201 89678982849773247865376401)
      ·
        refine ⟨67259237137329935899032301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89678982849773247865376401 67259237137329935899032301)
        ·
          refine ⟨25222213926498725962137113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67259237137329935899032301 25222213926498725962137113)
          ·
            refine ⟨18916660444874044471602835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25222213926498725962137113 18916660444874044471602835)
            ·
              refine ⟨28374990667311066707404253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18916660444874044471602835 28374990667311066707404253)
              ·
                refine ⟨10640621500241650015276595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28374990667311066707404253 10640621500241650015276595)
                ·
                  refine ⟨15960932250362475022914893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10640621500241650015276595 15960932250362475022914893)
                  ·
                    refine ⟨5985349593885928133593085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15960932250362475022914893 5985349593885928133593085)
                    ·
                      refine ⟨2244506097707223050097407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5985349593885928133593085 2244506097707223050097407)
                      ·
                        rfl

theorem cell23_4371160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 3, 1, 3, 3].length) (baseStart_4371160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4371160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4371160 prefixEnd_4371160 := by exact prefixLift 4371160
  have htrace : WordTrace (prefixWord ++ tailWord_4371160) baseStart_4371160 baseEnd_4371160 := by
    simpa [prefixWord, tailWord_4371160, baseEnd_4371160] using wordTrace_append hprefix tailTrace_4371160
  have hstable : (prefixWord ++ tailWord_4371160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4371160).length < 2 ^ (prefixWord ++ tailWord_4371160).sum := by decide
  have hdescent : baseEnd_4371160 < baseStart_4371160 := by decide
  rcases family_descends (prefixWord ++ tailWord_4371160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4371188 : List Nat := [2, 6, 1, 1, 2, 2, 1, 2, 2, 4]
def baseStart_4371188 : Nat := 118140960795 + 4371188 * 2 ^ 59
def prefixEnd_4371188 : Nat := 4983230072969 + 3 ^ 40 * 4371188 * 2
def baseEnd_4371188 : Nat := 748173491721849646849093

theorem tailTrace_4371188 : CollatzResearch.WordTrace tailWord_4371188 prefixEnd_4371188 748173491721849646849093 := by
  unfold tailWord_4371188
  simp only [CollatzResearch.WordTrace]
  refine ⟨79715162043969945160233109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106286882725293260213644145 79715162043969945160233109)
  ·
    refine ⟨3736648220811091179385927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 79715162043969945160233109 3736648220811091179385927)
    ·
      refine ⟨5604972331216636769078891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3736648220811091179385927 5604972331216636769078891)
      ·
        refine ⟨8407458496824955153618337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5604972331216636769078891 8407458496824955153618337)
        ·
          refine ⟨6305593872618716365213753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8407458496824955153618337 6305593872618716365213753)
          ·
            refine ⟨4729195404464037273910315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6305593872618716365213753 4729195404464037273910315)
            ·
              refine ⟨7093793106696055910865473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4729195404464037273910315 7093793106696055910865473)
              ·
                refine ⟨5320344830022041933149105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7093793106696055910865473 5320344830022041933149105)
                ·
                  refine ⟨3990258622516531449861829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5320344830022041933149105 3990258622516531449861829)
                  ·
                    refine ⟨748173491721849646849093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3990258622516531449861829 748173491721849646849093)
                    ·
                      rfl

theorem cell23_4371188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_4371188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4371188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4371188 prefixEnd_4371188 := by exact prefixLift 4371188
  have htrace : WordTrace (prefixWord ++ tailWord_4371188) baseStart_4371188 baseEnd_4371188 := by
    simpa [prefixWord, tailWord_4371188, baseEnd_4371188] using wordTrace_append hprefix tailTrace_4371188
  have hstable : (prefixWord ++ tailWord_4371188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4371188).length < 2 ^ (prefixWord ++ tailWord_4371188).sum := by decide
  have hdescent : baseEnd_4371188 < baseStart_4371188 := by decide
  rcases family_descends (prefixWord ++ tailWord_4371188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4371203 : List Nat := [1, 1, 1, 3, 2, 2, 1, 2, 4, 1, 5]
def baseStart_4371203 : Nat := 118140960795 + 4371203 * 2 ^ 59
def prefixEnd_4371203 : Nat := 4983230072969 + 3 ^ 40 * 4371203 * 2
def baseEnd_4371203 : Nat := 2244528177375366381859709

theorem tailTrace_4371203 : CollatzResearch.WordTrace tailWord_4371203 prefixEnd_4371203 2244528177375366381859709 := by
  unfold tailWord_4371203
  simp only [CollatzResearch.WordTrace]
  refine ⟨159430871182885547882262263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106287247455257031921508175 159430871182885547882262263)
  ·
    refine ⟨239146306774328321823393395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159430871182885547882262263 239146306774328321823393395)
    ·
      refine ⟨358719460161492482735090093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239146306774328321823393395 358719460161492482735090093)
      ·
        refine ⟨134519797560559681025658785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 358719460161492482735090093 134519797560559681025658785)
        ·
          refine ⟨100889848170419760769244089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134519797560559681025658785 100889848170419760769244089)
          ·
            refine ⟨75667386127814820576933067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100889848170419760769244089 75667386127814820576933067)
            ·
              refine ⟨113501079191722230865399601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75667386127814820576933067 113501079191722230865399601)
              ·
                refine ⟨85125809393791673149049701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113501079191722230865399601 85125809393791673149049701)
                ·
                  refine ⟨15961089261335938715446819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 85125809393791673149049701 15961089261335938715446819)
                  ·
                    refine ⟨23941633892003908073170229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15961089261335938715446819 23941633892003908073170229)
                    ·
                      refine ⟨2244528177375366381859709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23941633892003908073170229 2244528177375366381859709)
                      ·
                        rfl

theorem cell23_4371203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 4, 1, 5].length) (baseStart_4371203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4371203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4371203 prefixEnd_4371203 := by exact prefixLift 4371203
  have htrace : WordTrace (prefixWord ++ tailWord_4371203) baseStart_4371203 baseEnd_4371203 := by
    simpa [prefixWord, tailWord_4371203, baseEnd_4371203] using wordTrace_append hprefix tailTrace_4371203
  have hstable : (prefixWord ++ tailWord_4371203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4371203).length < 2 ^ (prefixWord ++ tailWord_4371203).sum := by decide
  have hdescent : baseEnd_4371203 < baseStart_4371203 := by decide
  rcases family_descends (prefixWord ++ tailWord_4371203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4371217 : List Nat := [1, 2, 2, 1, 1, 3, 5, 1, 1, 4, 2]
def baseStart_4371217 : Nat := 118140960795 + 4371217 * 2 ^ 59
def prefixEnd_4371217 : Nat := 4983230072969 + 3 ^ 40 * 4371217 * 2
def baseEnd_4371217 : Nat := 2244535366104529327084645

theorem tailTrace_4371217 : CollatzResearch.WordTrace tailWord_4371217 prefixEnd_4371217 2244535366104529327084645 := by
  unfold tailWord_4371217
  simp only [CollatzResearch.WordTrace]
  refine ⟨159431381804834828273271905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106287587869889885515514603 159431381804834828273271905)
  ·
    refine ⟨119573536353626121204953929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159431381804834828273271905 119573536353626121204953929)
    ·
      refine ⟨89680152265219590903715447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119573536353626121204953929 89680152265219590903715447)
      ·
        refine ⟨134520228397829386355573171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89680152265219590903715447 134520228397829386355573171)
        ·
          refine ⟨201780342596744079533359757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134520228397829386355573171 201780342596744079533359757)
          ·
            refine ⟨75667628473779029825009909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 201780342596744079533359757 75667628473779029825009909)
            ·
              refine ⟨7093840169416784046094679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 75667628473779029825009909 7093840169416784046094679)
              ·
                refine ⟨10640760254125176069142019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7093840169416784046094679 10640760254125176069142019)
                ·
                  refine ⟨15961140381187764103713029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10640760254125176069142019 15961140381187764103713029)
                  ·
                    refine ⟨2992713821472705769446193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15961140381187764103713029 2992713821472705769446193)
                    ·
                      refine ⟨2244535366104529327084645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2992713821472705769446193 2244535366104529327084645)
                      ·
                        rfl

theorem cell23_4371217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 4, 2].length) (baseStart_4371217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4371217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4371217 prefixEnd_4371217 := by exact prefixLift 4371217
  have htrace : WordTrace (prefixWord ++ tailWord_4371217) baseStart_4371217 baseEnd_4371217 := by
    simpa [prefixWord, tailWord_4371217, baseEnd_4371217] using wordTrace_append hprefix tailTrace_4371217
  have hstable : (prefixWord ++ tailWord_4371217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4371217).length < 2 ^ (prefixWord ++ tailWord_4371217).sum := by decide
  have hdescent : baseEnd_4371217 < baseStart_4371217 := by decide
  rcases family_descends (prefixWord ++ tailWord_4371217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4371234 : List Nat := [3, 3, 1, 1, 2, 2, 1, 2, 4, 2, 2]
def baseStart_4371234 : Nat := 118140960795 + 4371234 * 2 ^ 59
def prefixEnd_4371234 : Nat := 4983230072969 + 3 ^ 40 * 4371234 * 2
def baseEnd_4371234 : Nat := 2244544095275655760572067

theorem tailTrace_4371234 : CollatzResearch.WordTrace tailWord_4371234 prefixEnd_4371234 2244544095275655760572067 := by
  unfold tailWord_4371234
  simp only [CollatzResearch.WordTrace]
  refine ⟨39858000461443310044160189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106288001230515493451093837 39858000461443310044160189)
  ·
    refine ⟨14946750173041241266560071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39858000461443310044160189 14946750173041241266560071)
    ·
      refine ⟨22420125259561861899840107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14946750173041241266560071 22420125259561861899840107)
      ·
        refine ⟨33630187889342792849760161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22420125259561861899840107 33630187889342792849760161)
        ·
          refine ⟨25222640917007094637320121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33630187889342792849760161 25222640917007094637320121)
          ·
            refine ⟨18916980687755320977990091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25222640917007094637320121 18916980687755320977990091)
            ·
              refine ⟨28375471031632981466985137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18916980687755320977990091 28375471031632981466985137)
              ·
                refine ⟨21281603273724736100238853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28375471031632981466985137 21281603273724736100238853)
                ·
                  refine ⟨3990300613823388018794785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21281603273724736100238853 3990300613823388018794785)
                  ·
                    refine ⟨2992725460367541014096089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3990300613823388018794785 2992725460367541014096089)
                    ·
                      refine ⟨2244544095275655760572067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2992725460367541014096089 2244544095275655760572067)
                      ·
                        rfl

theorem cell23_4371234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 4, 2, 2].length) (baseStart_4371234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4371234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4371234 prefixEnd_4371234 := by exact prefixLift 4371234
  have htrace : WordTrace (prefixWord ++ tailWord_4371234) baseStart_4371234 baseEnd_4371234 := by
    simpa [prefixWord, tailWord_4371234, baseEnd_4371234] using wordTrace_append hprefix tailTrace_4371234
  have hstable : (prefixWord ++ tailWord_4371234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4371234).length < 2 ^ (prefixWord ++ tailWord_4371234).sum := by decide
  have hdescent : baseEnd_4371234 < baseStart_4371234 := by decide
  rcases family_descends (prefixWord ++ tailWord_4371234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4371283 : List Nat := [1, 1, 1, 2, 1, 1, 3, 3, 2, 8]
def baseStart_4371283 : Nat := 118140960795 + 4371283 * 2 ^ 59
def prefixEnd_4371283 : Nat := 4983230072969 + 3 ^ 40 * 4371283 * 2
def baseEnd_4371283 : Nat := 748189751942575356286447

theorem tailTrace_4371283 : CollatzResearch.WordTrace tailWord_4371283 prefixEnd_4371283 748189751942575356286447 := by
  unfold tailWord_4371283
  simp only [CollatzResearch.WordTrace]
  refine ⟨159433789022595721545174503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106289192681730481030116335 159433789022595721545174503)
  ·
    refine ⟨239150683533893582317761755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159433789022595721545174503 239150683533893582317761755)
    ·
      refine ⟨358726025300840373476642633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239150683533893582317761755 358726025300840373476642633)
      ·
        refine ⟨269044518975630280107481975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 358726025300840373476642633 269044518975630280107481975)
        ·
          refine ⟨403566778463445420161222963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 269044518975630280107481975 403566778463445420161222963)
          ·
            refine ⟨605350167695168130241834445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 403566778463445420161222963 605350167695168130241834445)
            ·
              refine ⟨227006312885688048840687917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 605350167695168130241834445 227006312885688048840687917)
              ·
                refine ⟨85127367332133018315257969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 227006312885688048840687917 85127367332133018315257969)
                ·
                  refine ⟨63845525499099763736443477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85127367332133018315257969 63845525499099763736443477)
                  ·
                    refine ⟨748189751942575356286447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 63845525499099763736443477 748189751942575356286447)
                    ·
                      rfl

theorem cell23_4371283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 8].length) (baseStart_4371283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4371283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4371283 prefixEnd_4371283 := by exact prefixLift 4371283
  have htrace : WordTrace (prefixWord ++ tailWord_4371283) baseStart_4371283 baseEnd_4371283 := by
    simpa [prefixWord, tailWord_4371283, baseEnd_4371283] using wordTrace_append hprefix tailTrace_4371283
  have hstable : (prefixWord ++ tailWord_4371283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4371283).length < 2 ^ (prefixWord ++ tailWord_4371283).sum := by decide
  have hdescent : baseEnd_4371283 < baseStart_4371283 := by decide
  rcases family_descends (prefixWord ++ tailWord_4371283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4371287 : List Nat := [1, 1, 3, 2, 4, 2, 2, 1, 2, 5]
def baseStart_4371287 : Nat := 118140960795 + 4371287 * 2 ^ 59
def prefixEnd_4371287 : Nat := 4983230072969 + 3 ^ 40 * 4371287 * 2
def baseEnd_4371287 : Nat := 748190436583448017736441

theorem tailTrace_4371287 : CollatzResearch.WordTrace tailWord_4371287 prefixEnd_4371287 748190436583448017736441 := by
  unfold tailWord_4371287
  simp only [CollatzResearch.WordTrace]
  refine ⟨159433934914581230228320115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106289289943054153485546743 159433934914581230228320115)
  ·
    refine ⟨239150902371871845342480173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159433934914581230228320115 239150902371871845342480173)
    ·
      refine ⟨89681588389451942003430065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 239150902371871845342480173 89681588389451942003430065)
      ·
        refine ⟨67261191292088956502572549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89681588389451942003430065 67261191292088956502572549)
        ·
          refine ⟨12611473367266679344232353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67261191292088956502572549 12611473367266679344232353)
          ·
            refine ⟨9458605025450009508174265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12611473367266679344232353 9458605025450009508174265)
            ·
              refine ⟨7093953769087507131130699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9458605025450009508174265 7093953769087507131130699)
              ·
                refine ⟨10640930653631260696696049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7093953769087507131130699 10640930653631260696696049)
                ·
                  refine ⟨7980697990223445522522037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10640930653631260696696049 7980697990223445522522037)
                  ·
                    refine ⟨748190436583448017736441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7980697990223445522522037 748190436583448017736441)
                    ·
                      rfl

theorem cell23_4371287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 1, 2, 5].length) (baseStart_4371287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4371287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4371287 prefixEnd_4371287 := by exact prefixLift 4371287
  have htrace : WordTrace (prefixWord ++ tailWord_4371287) baseStart_4371287 baseEnd_4371287 := by
    simpa [prefixWord, tailWord_4371287, baseEnd_4371287] using wordTrace_append hprefix tailTrace_4371287
  have hstable : (prefixWord ++ tailWord_4371287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4371287).length < 2 ^ (prefixWord ++ tailWord_4371287).sum := by decide
  have hdescent : baseEnd_4371287 < baseStart_4371287 := by decide
  rcases family_descends (prefixWord ++ tailWord_4371287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4371407 : List Nat := [1, 1, 2, 1, 1, 6, 1, 2, 4, 4]
def baseStart_4371407 : Nat := 118140960795 + 4371407 * 2 ^ 59
def prefixEnd_4371407 : Nat := 4983230072969 + 3 ^ 40 * 4371407 * 2
def baseEnd_4371407 : Nat := 748210975809627861236257

theorem tailTrace_4371407 : CollatzResearch.WordTrace tailWord_4371407 prefixEnd_4371407 748210975809627861236257 := by
  unfold tailWord_4371407
  simp only [CollatzResearch.WordTrace]
  refine ⟨159438311674146490722688475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106292207782764327148458983 159438311674146490722688475)
  ·
    refine ⟨239157467511219736084032713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159438311674146490722688475 239157467511219736084032713)
    ·
      refine ⟨179368100633414802063024535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 239157467511219736084032713 179368100633414802063024535)
      ·
        refine ⟨269052150950122203094536803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179368100633414802063024535 269052150950122203094536803)
        ·
          refine ⟨403578226425183304641805205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 269052150950122203094536803 403578226425183304641805205)
          ·
            refine ⟨18917729363680467405084619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 403578226425183304641805205 18917729363680467405084619)
            ·
              refine ⟨28376594045520701107626929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18917729363680467405084619 28376594045520701107626929)
              ·
                refine ⟨21282445534140525830720197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28376594045520701107626929 21282445534140525830720197)
                ·
                  refine ⟨3990458537651348593260037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21282445534140525830720197 3990458537651348593260037)
                  ·
                    refine ⟨748210975809627861236257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3990458537651348593260037 748210975809627861236257)
                    ·
                      rfl

theorem cell23_4371407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 4, 4].length) (baseStart_4371407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4371407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4371407 prefixEnd_4371407 := by exact prefixLift 4371407
  have htrace : WordTrace (prefixWord ++ tailWord_4371407) baseStart_4371407 baseEnd_4371407 := by
    simpa [prefixWord, tailWord_4371407, baseEnd_4371407] using wordTrace_append hprefix tailTrace_4371407
  have hstable : (prefixWord ++ tailWord_4371407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4371407).length < 2 ^ (prefixWord ++ tailWord_4371407).sum := by decide
  have hdescent : baseEnd_4371407 < baseStart_4371407 := by decide
  rcases family_descends (prefixWord ++ tailWord_4371407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4371417 : List Nat := [1, 2, 1, 2, 5, 1, 1, 3, 1, 1, 5]
def baseStart_4371417 : Nat := 118140960795 + 4371417 * 2 ^ 59
def prefixEnd_4371417 : Nat := 4983230072969 + 3 ^ 40 * 4371417 * 2
def baseEnd_4371417 : Nat := 2244638062235428544583725

theorem tailTrace_4371417 : CollatzResearch.WordTrace tailWord_4371417 prefixEnd_4371417 2244638062235428544583725 := by
  unfold tailWord_4371417
  simp only [CollatzResearch.WordTrace]
  refine ⟨159438676404110262430552505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106292450936073508287035003 159438676404110262430552505)
  ·
    refine ⟨119579007303082696822914379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159438676404110262430552505 119579007303082696822914379)
    ·
      refine ⟨179368510954624045234371569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119579007303082696822914379 179368510954624045234371569)
      ·
        refine ⟨134526383215968033925778677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179368510954624045234371569 134526383215968033925778677)
        ·
          refine ⟨12611848426497003180541751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 134526383215968033925778677 12611848426497003180541751)
          ·
            refine ⟨18917772639745504770812627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12611848426497003180541751 18917772639745504770812627)
            ·
              refine ⟨28376658959618257156218941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18917772639745504770812627 28376658959618257156218941)
              ·
                refine ⟨10641247109856846433582103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28376658959618257156218941 10641247109856846433582103)
                ·
                  refine ⟨15961870664785269650373155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10641247109856846433582103 15961870664785269650373155)
                  ·
                    refine ⟨23942805997177904475559733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15961870664785269650373155 23942805997177904475559733)
                    ·
                      refine ⟨2244638062235428544583725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23942805997177904475559733 2244638062235428544583725)
                      ·
                        rfl

theorem cell23_4371417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 3, 1, 1, 5].length) (baseStart_4371417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4371417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4371417 prefixEnd_4371417 := by exact prefixLift 4371417
  have htrace : WordTrace (prefixWord ++ tailWord_4371417) baseStart_4371417 baseEnd_4371417 := by
    simpa [prefixWord, tailWord_4371417, baseEnd_4371417] using wordTrace_append hprefix tailTrace_4371417
  have hstable : (prefixWord ++ tailWord_4371417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4371417).length < 2 ^ (prefixWord ++ tailWord_4371417).sum := by decide
  have hdescent : baseEnd_4371417 < baseStart_4371417 := by decide
  rcases family_descends (prefixWord ++ tailWord_4371417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4371440 : List Nat := [2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 6]
def baseStart_4371440 : Nat := 118140960795 + 4371440 * 2 ^ 59
def prefixEnd_4371440 : Nat := 4983230072969 + 3 ^ 40 * 4371440 * 2
def baseEnd_4371440 : Nat := 2244649872290481954596119

theorem tailTrace_4371440 : CollatzResearch.WordTrace tailWord_4371440 prefixEnd_4371440 2244649872290481954596119 := by
  unfold tailWord_4371440
  simp only [CollatzResearch.WordTrace]
  refine ⟨79719757641513468679319887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106293010188684624905759849 79719757641513468679319887)
  ·
    refine ⟨119579636462270203018979831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79719757641513468679319887 119579636462270203018979831)
    ·
      refine ⟨179369454693405304528469747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119579636462270203018979831 179369454693405304528469747)
      ·
        refine ⟨269054182040107956792704621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179369454693405304528469747 269054182040107956792704621)
        ·
          refine ⟨100895318265040483797264233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 269054182040107956792704621 100895318265040483797264233)
          ·
            refine ⟨75671488698780362847948175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100895318265040483797264233 75671488698780362847948175)
            ·
              refine ⟨113507233048170544271922263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75671488698780362847948175 113507233048170544271922263)
              ·
                refine ⟨170260849572255816407883395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113507233048170544271922263 170260849572255816407883395)
                ·
                  refine ⟨255391274358383724611825093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 170260849572255816407883395 255391274358383724611825093)
                  ·
                    refine ⟨47885863942196948364717205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 255391274358383724611825093 47885863942196948364717205)
                    ·
                      refine ⟨2244649872290481954596119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47885863942196948364717205 2244649872290481954596119)
                      ·
                        rfl

theorem cell23_4371440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 6].length) (baseStart_4371440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4371440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4371440 prefixEnd_4371440 := by exact prefixLift 4371440
  have htrace : WordTrace (prefixWord ++ tailWord_4371440) baseStart_4371440 baseEnd_4371440 := by
    simpa [prefixWord, tailWord_4371440, baseEnd_4371440] using wordTrace_append hprefix tailTrace_4371440
  have hstable : (prefixWord ++ tailWord_4371440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4371440).length < 2 ^ (prefixWord ++ tailWord_4371440).sum := by decide
  have hdescent : baseEnd_4371440 < baseStart_4371440 := by decide
  rcases family_descends (prefixWord ++ tailWord_4371440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4371441 : List Nat := [1, 2, 2, 2, 4, 1, 4, 1, 2, 4]
def baseStart_4371441 : Nat := 118140960795 + 4371441 * 2 ^ 59
def prefixEnd_4371441 : Nat := 4983230072969 + 3 ^ 40 * 4371441 * 2
def baseEnd_4371441 : Nat := 748216795257045483561205

theorem tailTrace_4371441 : CollatzResearch.WordTrace tailWord_4371441 prefixEnd_4371441 748216795257045483561205 := by
  unfold tailWord_4371441
  simp only [CollatzResearch.WordTrace]
  refine ⟨159439551756023314529426177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106293034504015543019617451 159439551756023314529426177)
  ·
    refine ⟨119579663817017485897069633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159439551756023314529426177 119579663817017485897069633)
    ·
      refine ⟨89684747862763114422802225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119579663817017485897069633 89684747862763114422802225)
      ·
        refine ⟨67263560897072335817101669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89684747862763114422802225 67263560897072335817101669)
        ·
          refine ⟨12611917668201062965706563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67263560897072335817101669 12611917668201062965706563)
          ·
            refine ⟨18917876502301594448559845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12611917668201062965706563 18917876502301594448559845)
            ·
              refine ⟨3547101844181548959104971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18917876502301594448559845 3547101844181548959104971)
              ·
                refine ⟨5320652766272323438657457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3547101844181548959104971 5320652766272323438657457)
                ·
                  refine ⟨3990489574704242578993093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5320652766272323438657457 3990489574704242578993093)
                  ·
                    refine ⟨748216795257045483561205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3990489574704242578993093 748216795257045483561205)
                    ·
                      rfl

theorem cell23_4371441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 4, 1, 2, 4].length) (baseStart_4371441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4371441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4371441 prefixEnd_4371441 := by exact prefixLift 4371441
  have htrace : WordTrace (prefixWord ++ tailWord_4371441) baseStart_4371441 baseEnd_4371441 := by
    simpa [prefixWord, tailWord_4371441, baseEnd_4371441] using wordTrace_append hprefix tailTrace_4371441
  have hstable : (prefixWord ++ tailWord_4371441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4371441).length < 2 ^ (prefixWord ++ tailWord_4371441).sum := by decide
  have hdescent : baseEnd_4371441 < baseStart_4371441 := by decide
  rcases family_descends (prefixWord ++ tailWord_4371441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4371445 : List Nat := [1, 3, 5, 2, 2, 1, 1, 2, 1, 5]
def baseStart_4371445 : Nat := 118140960795 + 4371445 * 2 ^ 59
def prefixEnd_4371445 : Nat := 4983230072969 + 3 ^ 40 * 4371445 * 2
def baseEnd_4371445 : Nat := 748217479897918145011199

theorem tailTrace_4371445 : CollatzResearch.WordTrace tailWord_4371445 prefixEnd_4371445 748217479897918145011199 := by
  unfold tailWord_4371445
  simp only [CollatzResearch.WordTrace]
  refine ⟨159439697648008823212571789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106293131765339215475047859 159439697648008823212571789)
  ·
    refine ⟨59789886618003308704714421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159439697648008823212571789 59789886618003308704714421)
    ·
      refine ⟨5605301870437810191066977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59789886618003308704714421 5605301870437810191066977)
      ·
        refine ⟨4203976402828357643300233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5605301870437810191066977 4203976402828357643300233)
        ·
          refine ⟨3152982302121268232475175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4203976402828357643300233 3152982302121268232475175)
          ·
            refine ⟨4729473453181902348712763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3152982302121268232475175 4729473453181902348712763)
            ·
              refine ⟨7094210179772853523069145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4729473453181902348712763 7094210179772853523069145)
              ·
                refine ⟨5320657634829640142301859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7094210179772853523069145 5320657634829640142301859)
                ·
                  refine ⟨7980986452244460213452789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5320657634829640142301859 7980986452244460213452789)
                  ·
                    refine ⟨748217479897918145011199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7980986452244460213452789 748217479897918145011199)
                    ·
                      rfl

theorem cell23_4371445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_4371445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4371445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4371445 prefixEnd_4371445 := by exact prefixLift 4371445
  have htrace : WordTrace (prefixWord ++ tailWord_4371445) baseStart_4371445 baseEnd_4371445 := by
    simpa [prefixWord, tailWord_4371445, baseEnd_4371445] using wordTrace_append hprefix tailTrace_4371445
  have hstable : (prefixWord ++ tailWord_4371445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4371445).length < 2 ^ (prefixWord ++ tailWord_4371445).sum := by decide
  have hdescent : baseEnd_4371445 < baseStart_4371445 := by decide
  rcases family_descends (prefixWord ++ tailWord_4371445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4371464 : List Nat := [2, 1, 3, 2, 1, 4, 1, 2, 1, 3, 3]
def baseStart_4371464 : Nat := 118140960795 + 4371464 * 2 ^ 59
def prefixEnd_4371464 : Nat := 4983230072969 + 3 ^ 40 * 4371464 * 2
def baseEnd_4371464 : Nat := 2244662195826189860696009

theorem tailTrace_4371464 : CollatzResearch.WordTrace tailWord_4371464 prefixEnd_4371464 2244662195826189860696009 := by
  unfold tailWord_4371464
  simp only [CollatzResearch.WordTrace]
  refine ⟨79720195317469994728756723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106293593756626659638342297 79720195317469994728756723)
  ·
    refine ⟨119580292976204992093135085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79720195317469994728756723 119580292976204992093135085)
    ·
      refine ⟨44842609866076872034925657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119580292976204992093135085 44842609866076872034925657)
      ·
        refine ⟨33631957399557654026194243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44842609866076872034925657 33631957399557654026194243)
        ·
          refine ⟨50447936099336481039291365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33631957399557654026194243 50447936099336481039291365)
          ·
            refine ⟨9458988018625590194867131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50447936099336481039291365 9458988018625590194867131)
            ·
              refine ⟨14188482027938385292300697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9458988018625590194867131 14188482027938385292300697)
              ·
                refine ⟨10641361520953788969225523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14188482027938385292300697 10641361520953788969225523)
                ·
                  refine ⟨15962042281430683453838285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10641361520953788969225523 15962042281430683453838285)
                  ·
                    refine ⟨5985765855536506295189357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15962042281430683453838285 5985765855536506295189357)
                    ·
                      refine ⟨2244662195826189860696009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5985765855536506295189357 2244662195826189860696009)
                      ·
                        rfl

theorem cell23_4371464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 2, 1, 3, 3].length) (baseStart_4371464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4371464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4371464 prefixEnd_4371464 := by exact prefixLift 4371464
  have htrace : WordTrace (prefixWord ++ tailWord_4371464) baseStart_4371464 baseEnd_4371464 := by
    simpa [prefixWord, tailWord_4371464, baseEnd_4371464] using wordTrace_append hprefix tailTrace_4371464
  have hstable : (prefixWord ++ tailWord_4371464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4371464).length < 2 ^ (prefixWord ++ tailWord_4371464).sum := by decide
  have hdescent : baseEnd_4371464 < baseStart_4371464 := by decide
  rcases family_descends (prefixWord ++ tailWord_4371464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4371487 : List Nat := [1, 1, 2, 4, 1, 3, 1, 1, 2, 3, 4]
def baseStart_4371487 : Nat := 118140960795 + 4371487 * 2 ^ 59
def prefixEnd_4371487 : Nat := 4983230072969 + 3 ^ 40 * 4371487 * 2
def baseEnd_4371487 : Nat := 2244674005881243270708403

theorem tailTrace_4371487 : CollatzResearch.WordTrace tailWord_4371487 prefixEnd_4371487 2244674005881243270708403 := by
  unfold tailWord_4371487
  simp only [CollatzResearch.WordTrace]
  refine ⟨159441229513856664385600715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106294153009237776257067143 159441229513856664385600715)
  ·
    refine ⟨239161844270784996578401073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159441229513856664385600715 239161844270784996578401073)
    ·
      refine ⟨179371383203088747433800805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 239161844270784996578401073 179371383203088747433800805)
      ·
        refine ⟨33632134350579140143837651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 179371383203088747433800805 33632134350579140143837651)
        ·
          refine ⟨50448201525868710215756477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33632134350579140143837651 50448201525868710215756477)
          ·
            refine ⟨18918075572200766330908679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50448201525868710215756477 18918075572200766330908679)
            ·
              refine ⟨28377113358301149496363019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18918075572200766330908679 28377113358301149496363019)
              ·
                refine ⟨42565670037451724244544529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28377113358301149496363019 42565670037451724244544529)
                ·
                  refine ⟨31924252528088793183408397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42565670037451724244544529 31924252528088793183408397)
                  ·
                    refine ⟨11971594698033297443778149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31924252528088793183408397 11971594698033297443778149)
                    ·
                      refine ⟨2244674005881243270708403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11971594698033297443778149 2244674005881243270708403)
                      ·
                        rfl

theorem cell23_4371487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_4371487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4371487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4371487 prefixEnd_4371487 := by exact prefixLift 4371487
  have htrace : WordTrace (prefixWord ++ tailWord_4371487) baseStart_4371487 baseEnd_4371487 := by
    simpa [prefixWord, tailWord_4371487, baseEnd_4371487] using wordTrace_append hprefix tailTrace_4371487
  have hstable : (prefixWord ++ tailWord_4371487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4371487).length < 2 ^ (prefixWord ++ tailWord_4371487).sum := by decide
  have hdescent : baseEnd_4371487 < baseStart_4371487 := by decide
  rcases family_descends (prefixWord ++ tailWord_4371487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4371507 : List Nat := [1, 1, 1, 2, 4, 1, 1, 1, 4, 4, 3]
def baseStart_4371507 : Nat := 118140960795 + 4371507 * 2 ^ 59
def prefixEnd_4371507 : Nat := 4983230072969 + 3 ^ 40 * 4371507 * 2
def baseEnd_4371507 : Nat := 2244684275494333192458311

theorem tailTrace_4371507 : CollatzResearch.WordTrace tailWord_4371507 prefixEnd_4371507 2244684275494333192458311 := by
  unfold tailWord_4371507
  simp only [CollatzResearch.WordTrace]
  refine ⟨159441958973784207801328775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106294639315856138534219183 159441958973784207801328775)
  ·
    refine ⟨239162938460676311701993163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159441958973784207801328775 239162938460676311701993163)
    ·
      refine ⟨358744407691014467552989745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239162938460676311701993163 358744407691014467552989745)
      ·
        refine ⟨269058305768260850664742309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 358744407691014467552989745 269058305768260850664742309)
        ·
          refine ⟨50448432331548909499639183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 269058305768260850664742309 50448432331548909499639183)
          ·
            refine ⟨75672648497323364249458775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50448432331548909499639183 75672648497323364249458775)
            ·
              refine ⟨113508972745985046374188163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75672648497323364249458775 113508972745985046374188163)
              ·
                refine ⟨170263459118977569561282245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113508972745985046374188163 170263459118977569561282245)
                ·
                  refine ⟨31924398584808294292740421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 170263459118977569561282245 31924398584808294292740421)
                  ·
                    refine ⟨5985824734651555179888829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31924398584808294292740421 5985824734651555179888829)
                    ·
                      refine ⟨2244684275494333192458311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5985824734651555179888829 2244684275494333192458311)
                      ·
                        rfl

theorem cell23_4371507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 4, 3].length) (baseStart_4371507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4371507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4371507 prefixEnd_4371507 := by exact prefixLift 4371507
  have htrace : WordTrace (prefixWord ++ tailWord_4371507) baseStart_4371507 baseEnd_4371507 := by
    simpa [prefixWord, tailWord_4371507, baseEnd_4371507] using wordTrace_append hprefix tailTrace_4371507
  have hstable : (prefixWord ++ tailWord_4371507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4371507).length < 2 ^ (prefixWord ++ tailWord_4371507).sum := by decide
  have hdescent : baseEnd_4371507 < baseStart_4371507 := by decide
  rcases family_descends (prefixWord ++ tailWord_4371507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4371508 : List Nat := [2, 5, 1, 2, 1, 1, 2, 1, 3, 3, 2]
def baseStart_4371508 : Nat := 118140960795 + 4371508 * 2 ^ 59
def prefixEnd_4371508 : Nat := 4983230072969 + 3 ^ 40 * 4371508 * 2
def baseEnd_4371508 : Nat := 2244684788974987688545807

theorem tailTrace_4371508 : CollatzResearch.WordTrace tailWord_4371508 prefixEnd_4371508 2244684788974987688545807 := by
  unfold tailWord_4371508
  simp only [CollatzResearch.WordTrace]
  refine ⟨79720997723390292486057589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106294663631187056648076785 79720997723390292486057589)
  ·
    refine ⟨7473843536567839920567899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 79720997723390292486057589 7473843536567839920567899)
    ·
      refine ⟨11210765304851759880851849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7473843536567839920567899 11210765304851759880851849)
      ·
        refine ⟨8408073978638819910638887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11210765304851759880851849 8408073978638819910638887)
        ·
          refine ⟨12612110967958229865958331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8408073978638819910638887 12612110967958229865958331)
          ·
            refine ⟨18918166451937344798937497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12612110967958229865958331 18918166451937344798937497)
            ·
              refine ⟨14188624838953008599203123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18918166451937344798937497 14188624838953008599203123)
              ·
                refine ⟨21282937258429512898804685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14188624838953008599203123 21282937258429512898804685)
                ·
                  refine ⟨7981101471911067337051757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21282937258429512898804685 7981101471911067337051757)
                  ·
                    refine ⟨2992913051966650251394409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7981101471911067337051757 2992913051966650251394409)
                    ·
                      refine ⟨2244684788974987688545807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2992913051966650251394409 2244684788974987688545807)
                      ·
                        rfl

theorem cell23_4371508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_4371508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4371508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4371508 prefixEnd_4371508 := by exact prefixLift 4371508
  have htrace : WordTrace (prefixWord ++ tailWord_4371508) baseStart_4371508 baseEnd_4371508 := by
    simpa [prefixWord, tailWord_4371508, baseEnd_4371508] using wordTrace_append hprefix tailTrace_4371508
  have hstable : (prefixWord ++ tailWord_4371508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4371508).length < 2 ^ (prefixWord ++ tailWord_4371508).sum := by decide
  have hdescent : baseEnd_4371508 < baseStart_4371508 := by decide
  rcases family_descends (prefixWord ++ tailWord_4371508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4371538 : List Nat := [3, 2, 2, 1, 3, 2, 1, 1, 4, 2, 2]
def baseStart_4371538 : Nat := 118140960795 + 4371538 * 2 ^ 59
def prefixEnd_4371538 : Nat := 4983230072969 + 3 ^ 40 * 4371538 * 2
def baseEnd_4371538 : Nat := 2244700193394622571170669

theorem tailTrace_4371538 : CollatzResearch.WordTrace tailWord_4371538 prefixEnd_4371538 2244700193394622571170669 := by
  unfold tailWord_4371538
  simp only [CollatzResearch.WordTrace]
  refine ⟨39860772409167975023926817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106295393091114600063804845 39860772409167975023926817)
  ·
    refine ⟨29895579306875981267945113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39860772409167975023926817 29895579306875981267945113)
    ·
      refine ⟨22421684480156985950958835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29895579306875981267945113 22421684480156985950958835)
      ·
        refine ⟨33632526720235478926438253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22421684480156985950958835 33632526720235478926438253)
        ·
          refine ⟨12612197520088304597414345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33632526720235478926438253 12612197520088304597414345)
          ·
            refine ⟨9459148140066228448060759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12612197520088304597414345 9459148140066228448060759)
            ·
              refine ⟨14188722210099342672091139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9459148140066228448060759 14188722210099342672091139)
              ·
                refine ⟨21283083315149014008136709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14188722210099342672091139 21283083315149014008136709)
                ·
                  refine ⟨3990578121590440126525633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21283083315149014008136709 3990578121590440126525633)
                  ·
                    refine ⟨2992933591192830094894225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3990578121590440126525633 2992933591192830094894225)
                    ·
                      refine ⟨2244700193394622571170669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2992933591192830094894225 2244700193394622571170669)
                      ·
                        rfl

theorem cell23_4371538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 4, 2, 2].length) (baseStart_4371538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4371538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4371538 prefixEnd_4371538 := by exact prefixLift 4371538
  have htrace : WordTrace (prefixWord ++ tailWord_4371538) baseStart_4371538 baseEnd_4371538 := by
    simpa [prefixWord, tailWord_4371538, baseEnd_4371538] using wordTrace_append hprefix tailTrace_4371538
  have hstable : (prefixWord ++ tailWord_4371538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4371538).length < 2 ^ (prefixWord ++ tailWord_4371538).sum := by decide
  have hdescent : baseEnd_4371538 < baseStart_4371538 := by decide
  rcases family_descends (prefixWord ++ tailWord_4371538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4371544 : List Nat := [2, 1, 2, 2, 1, 3, 1, 6, 5]
def baseStart_4371544 : Nat := 118140960795 + 4371544 * 2 ^ 59
def prefixEnd_4371544 : Nat := 4983230072969 + 3 ^ 40 * 4371544 * 2
def baseEnd_4371544 : Nat := 249411474919838838632849

theorem tailTrace_4371544 : CollatzResearch.WordTrace tailWord_4371544 prefixEnd_4371544 249411474919838838632849 := by
  unfold tailWord_4371544
  simp only [CollatzResearch.WordTrace]
  refine ⟨79721654237325081560212843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106295538983100108746950457 79721654237325081560212843)
  ·
    refine ⟨119582481355987622340319265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79721654237325081560212843 119582481355987622340319265)
    ·
      refine ⟨89686861016990716755239449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119582481355987622340319265 89686861016990716755239449)
      ·
        refine ⟨67265145762743037566429587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89686861016990716755239449 67265145762743037566429587)
        ·
          refine ⟨100897718644114556349644381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67265145762743037566429587 100897718644114556349644381)
          ·
            refine ⟨37836644491542958631116643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100897718644114556349644381 37836644491542958631116643)
            ·
              refine ⟨56754966737314437946674965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37836644491542958631116643 56754966737314437946674965)
              ·
                refine ⟨2660389065811614278750389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 56754966737314437946674965 2660389065811614278750389)
                ·
                  refine ⟨249411474919838838632849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2660389065811614278750389 249411474919838838632849)
                  ·
                    rfl

theorem cell23_4371544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 6, 5].length) (baseStart_4371544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4371544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4371544 prefixEnd_4371544 := by exact prefixLift 4371544
  have htrace : WordTrace (prefixWord ++ tailWord_4371544) baseStart_4371544 baseEnd_4371544 := by
    simpa [prefixWord, tailWord_4371544, baseEnd_4371544] using wordTrace_append hprefix tailTrace_4371544
  have hstable : (prefixWord ++ tailWord_4371544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4371544).length < 2 ^ (prefixWord ++ tailWord_4371544).sum := by decide
  have hdescent : baseEnd_4371544 < baseStart_4371544 := by decide
  rcases family_descends (prefixWord ++ tailWord_4371544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4371557 : List Nat := [1, 3, 1, 3, 2, 1, 1, 1, 3, 7]
def baseStart_4371557 : Nat := 118140960795 + 4371557 * 2 ^ 59
def prefixEnd_4371557 : Nat := 4983230072969 + 3 ^ 40 * 4371557 * 2
def baseEnd_4371557 : Nat := 748236649842352665611027

theorem tailTrace_4371557 : CollatzResearch.WordTrace tailWord_4371557 prefixEnd_4371557 748236649842352665611027 := by
  unfold tailWord_4371557
  simp only [CollatzResearch.WordTrace]
  refine ⟨159443782623603066340648925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106295855082402044227099283 159443782623603066340648925)
  ·
    refine ⟨59791418483851149877743347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159443782623603066340648925 59791418483851149877743347)
    ·
      refine ⟨89687127725776724816615021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59791418483851149877743347 89687127725776724816615021)
      ·
        refine ⟨33632672897166271806230633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89687127725776724816615021 33632672897166271806230633)
        ·
          refine ⟨25224504672874703854672975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33632672897166271806230633 25224504672874703854672975)
          ·
            refine ⟨37836757009312055782009463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25224504672874703854672975 37836757009312055782009463)
            ·
              refine ⟨56755135513968083673014195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37836757009312055782009463 56755135513968083673014195)
              ·
                refine ⟨85132703270952125509521293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56755135513968083673014195 85132703270952125509521293)
                ·
                  refine ⟨31924763726607047066070485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 85132703270952125509521293 31924763726607047066070485)
                  ·
                    refine ⟨748236649842352665611027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31924763726607047066070485 748236649842352665611027)
                    ·
                      rfl

theorem cell23_4371557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 7].length) (baseStart_4371557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4371557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4371557 prefixEnd_4371557 := by exact prefixLift 4371557
  have htrace : WordTrace (prefixWord ++ tailWord_4371557) baseStart_4371557 baseEnd_4371557 := by
    simpa [prefixWord, tailWord_4371557, baseEnd_4371557] using wordTrace_append hprefix tailTrace_4371557
  have hstable : (prefixWord ++ tailWord_4371557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4371557).length < 2 ^ (prefixWord ++ tailWord_4371557).sum := by decide
  have hdescent : baseEnd_4371557 < baseStart_4371557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4371557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4371574 : List Nat := [5, 1, 1, 2, 1, 1, 1, 3, 1, 7]
def baseStart_4371574 : Nat := 118140960795 + 4371574 * 2 ^ 59
def prefixEnd_4371574 : Nat := 4983230072969 + 3 ^ 40 * 4371574 * 2
def baseEnd_4371574 : Nat := 748239559566061476773501

theorem tailTrace_4371574 : CollatzResearch.WordTrace tailWord_4371574 prefixEnd_4371574 748239559566061476773501 := by
  unfold tailWord_4371574
  simp only [CollatzResearch.WordTrace]
  refine ⟨9965275166533842390251111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 106296268443027652162678517 9965275166533842390251111)
  ·
    refine ⟨14947912749800763585376667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9965275166533842390251111 14947912749800763585376667)
    ·
      refine ⟨22421869124701145378065001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14947912749800763585376667 22421869124701145378065001)
      ·
        refine ⟨16816401843525859033548751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22421869124701145378065001 16816401843525859033548751)
        ·
          refine ⟨25224602765288788550323127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16816401843525859033548751 25224602765288788550323127)
          ·
            refine ⟨37836904147933182825484691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25224602765288788550323127 37836904147933182825484691)
            ·
              refine ⟨56755356221899774238227037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37836904147933182825484691 56755356221899774238227037)
              ·
                refine ⟨21283258583212415339335139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56755356221899774238227037 21283258583212415339335139)
                ·
                  refine ⟨31924887874818623009002709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21283258583212415339335139 31924887874818623009002709)
                  ·
                    refine ⟨748239559566061476773501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31924887874818623009002709 748239559566061476773501)
                    ·
                      rfl

theorem cell23_4371574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_4371574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4371574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4371574 prefixEnd_4371574 := by exact prefixLift 4371574
  have htrace : WordTrace (prefixWord ++ tailWord_4371574) baseStart_4371574 baseEnd_4371574 := by
    simpa [prefixWord, tailWord_4371574, baseEnd_4371574] using wordTrace_append hprefix tailTrace_4371574
  have hstable : (prefixWord ++ tailWord_4371574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4371574).length < 2 ^ (prefixWord ++ tailWord_4371574).sum := by decide
  have hdescent : baseEnd_4371574 < baseStart_4371574 := by decide
  rcases family_descends (prefixWord ++ tailWord_4371574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4371671 : List Nat := [1, 1, 3, 2, 1, 2, 2, 2, 4, 3, 2]
def baseStart_4371671 : Nat := 118140960795 + 4371671 * 2 ^ 59
def prefixEnd_4371671 : Nat := 4983230072969 + 3 ^ 40 * 4371671 * 2
def baseEnd_4371671 : Nat := 2244768486321670550807557

theorem tailTrace_4371671 : CollatzResearch.WordTrace tailWord_4371671 prefixEnd_4371671 2244768486321670550807557 := by
  unfold tailWord_4371671
  simp only [CollatzResearch.WordTrace]
  refine ⟨159447940545190063810298867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106298627030126709206865911 159447940545190063810298867)
  ·
    refine ⟨239171910817785095715448301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159447940545190063810298867 239171910817785095715448301)
    ·
      refine ⟨89689466556669410893293113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 239171910817785095715448301 89689466556669410893293113)
      ·
        refine ⟨67267099917502058169969835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89689466556669410893293113 67267099917502058169969835)
        ·
          refine ⟨100900649876253087254954753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67267099917502058169969835 100900649876253087254954753)
          ·
            refine ⟨75675487407189815441216065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100900649876253087254954753 75675487407189815441216065)
            ·
              refine ⟨56756615555392361580912049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75675487407189815441216065 56756615555392361580912049)
              ·
                refine ⟨42567461666544271185684037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56756615555392361580912049 42567461666544271185684037)
                ·
                  refine ⟨7981399062477050847315757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42567461666544271185684037 7981399062477050847315757)
                  ·
                    refine ⟨2993024648428894067743409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7981399062477050847315757 2993024648428894067743409)
                    ·
                      refine ⟨2244768486321670550807557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2993024648428894067743409 2244768486321670550807557)
                      ·
                        rfl

theorem cell23_4371671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 4, 3, 2].length) (baseStart_4371671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4371671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4371671 prefixEnd_4371671 := by exact prefixLift 4371671
  have htrace : WordTrace (prefixWord ++ tailWord_4371671) baseStart_4371671 baseEnd_4371671 := by
    simpa [prefixWord, tailWord_4371671, baseEnd_4371671] using wordTrace_append hprefix tailTrace_4371671
  have hstable : (prefixWord ++ tailWord_4371671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4371671).length < 2 ^ (prefixWord ++ tailWord_4371671).sum := by decide
  have hdescent : baseEnd_4371671 < baseStart_4371671 := by decide
  rcases family_descends (prefixWord ++ tailWord_4371671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4371698 : List Nat := [3, 2, 1, 3, 3, 1, 1, 3, 1, 5]
def baseStart_4371698 : Nat := 118140960795 + 4371698 * 2 ^ 59
def prefixEnd_4371698 : Nat := 4983230072969 + 3 ^ 40 * 4371698 * 2
def baseEnd_4371698 : Nat := 748260783433113981723311

theorem tailTrace_4371698 : CollatzResearch.WordTrace tailWord_4371698 prefixEnd_4371698 748260783433113981723311 := by
  unfold tailWord_4371698
  simp only [CollatzResearch.WordTrace]
  refine ⟨39862231329023061855382937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106299283544061498281021165 39862231329023061855382937)
  ·
    refine ⟨29896673496767296391537203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39862231329023061855382937 29896673496767296391537203)
    ·
      refine ⟨44845010245150944587305805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29896673496767296391537203 44845010245150944587305805)
      ·
        refine ⟨16816878841931604220239677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44845010245150944587305805 16816878841931604220239677)
        ·
          refine ⟨6306329565724351582589879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16816878841931604220239677 6306329565724351582589879)
          ·
            refine ⟨9459494348586527373884819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6306329565724351582589879 9459494348586527373884819)
            ·
              refine ⟨14189241522879791060827229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9459494348586527373884819 14189241522879791060827229)
              ·
                refine ⟨5320965571079921647810211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14189241522879791060827229 5320965571079921647810211)
                ·
                  refine ⟨7981448356619882471715317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5320965571079921647810211 7981448356619882471715317)
                  ·
                    refine ⟨748260783433113981723311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7981448356619882471715317 748260783433113981723311)
                    ·
                      rfl

theorem cell23_4371698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 3, 1, 5].length) (baseStart_4371698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4371698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4371698 prefixEnd_4371698 := by exact prefixLift 4371698
  have htrace : WordTrace (prefixWord ++ tailWord_4371698) baseStart_4371698 baseEnd_4371698 := by
    simpa [prefixWord, tailWord_4371698, baseEnd_4371698] using wordTrace_append hprefix tailTrace_4371698
  have hstable : (prefixWord ++ tailWord_4371698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4371698).length < 2 ^ (prefixWord ++ tailWord_4371698).sum := by decide
  have hdescent : baseEnd_4371698 < baseStart_4371698 := by decide
  rcases family_descends (prefixWord ++ tailWord_4371698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4371711 : List Nat := [1, 1, 2, 2, 1, 6, 1, 1, 4, 4]
def baseStart_4371711 : Nat := 118140960795 + 4371711 * 2 ^ 59
def prefixEnd_4371711 : Nat := 4983230072969 + 3 ^ 40 * 4371711 * 2
def baseEnd_4371711 : Nat := 748263008515950131435791

theorem tailTrace_4371711 : CollatzResearch.WordTrace tailWord_4371711 prefixEnd_4371711 748263008515950131435791 := by
  unfold tailWord_4371711
  simp only [CollatzResearch.WordTrace]
  refine ⟨159449399465045150641754987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106299599643363433761169991 159449399465045150641754987)
  ·
    refine ⟨239174099197567725962632481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159449399465045150641754987 239174099197567725962632481)
    ·
      refine ⟨179380574398175794471974361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 239174099197567725962632481 179380574398175794471974361)
      ·
        refine ⟨134535430798631845853980771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179380574398175794471974361 134535430798631845853980771)
        ·
          refine ⟨201803146197947768780971157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134535430798631845853980771 201803146197947768780971157)
          ·
            refine ⟨9459522478028801661608023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 201803146197947768780971157 9459522478028801661608023)
            ·
              refine ⟨14189283717043202492412035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9459522478028801661608023 14189283717043202492412035)
              ·
                refine ⟨21283925575564803738618053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14189283717043202492412035 21283925575564803738618053)
                ·
                  refine ⟨3990736045418400700990885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21283925575564803738618053 3990736045418400700990885)
                  ·
                    refine ⟨748263008515950131435791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3990736045418400700990885 748263008515950131435791)
                    ·
                      rfl

theorem cell23_4371711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 4, 4].length) (baseStart_4371711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4371711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4371711 prefixEnd_4371711 := by exact prefixLift 4371711
  have htrace : WordTrace (prefixWord ++ tailWord_4371711) baseStart_4371711 baseEnd_4371711 := by
    simpa [prefixWord, tailWord_4371711, baseEnd_4371711] using wordTrace_append hprefix tailTrace_4371711
  have hstable : (prefixWord ++ tailWord_4371711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4371711).length < 2 ^ (prefixWord ++ tailWord_4371711).sum := by decide
  have hdescent : baseEnd_4371711 < baseStart_4371711 := by decide
  rcases family_descends (prefixWord ++ tailWord_4371711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4371738 : List Nat := [3, 1, 1, 3, 3, 1, 1, 4, 1, 2, 3]
def baseStart_4371738 : Nat := 118140960795 + 4371738 * 2 ^ 59
def prefixEnd_4371738 : Nat := 4983230072969 + 3 ^ 40 * 4371738 * 2
def baseEnd_4371738 : Nat := 2244802889525521788669749

theorem tailTrace_4371738 : CollatzResearch.WordTrace tailWord_4371738 prefixEnd_4371738 2244802889525521788669749 := by
  unfold tailWord_4371738
  simp only [CollatzResearch.WordTrace]
  refine ⟨39862596058986833563246967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106300256157298222835325245 39862596058986833563246967)
  ·
    refine ⟨59793894088480250344870451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39862596058986833563246967 59793894088480250344870451)
    ·
      refine ⟨89690841132720375517305677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59793894088480250344870451 89690841132720375517305677)
      ·
        refine ⟨33634065424770140818989629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89690841132720375517305677 33634065424770140818989629)
        ·
          refine ⟨12612774534288802807121111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33634065424770140818989629 12612774534288802807121111)
          ·
            refine ⟨18919161801433204210681667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12612774534288802807121111 18919161801433204210681667)
            ·
              refine ⟨28378742702149806316022501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18919161801433204210681667 28378742702149806316022501)
              ·
                refine ⟨5321014256653088684254219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28378742702149806316022501 5321014256653088684254219)
                ·
                  refine ⟨7981521384979633026381329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5321014256653088684254219 7981521384979633026381329)
                  ·
                    refine ⟨5986141038734724769785997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7981521384979633026381329 5986141038734724769785997)
                    ·
                      refine ⟨2244802889525521788669749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5986141038734724769785997 2244802889525521788669749)
                      ·
                        rfl

theorem cell23_4371738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 4, 1, 2, 3].length) (baseStart_4371738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4371738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4371738 prefixEnd_4371738 := by exact prefixLift 4371738
  have htrace : WordTrace (prefixWord ++ tailWord_4371738) baseStart_4371738 baseEnd_4371738 := by
    simpa [prefixWord, tailWord_4371738, baseEnd_4371738] using wordTrace_append hprefix tailTrace_4371738
  have hstable : (prefixWord ++ tailWord_4371738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4371738).length < 2 ^ (prefixWord ++ tailWord_4371738).sum := by decide
  have hdescent : baseEnd_4371738 < baseStart_4371738 := by decide
  rcases family_descends (prefixWord ++ tailWord_4371738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4371741 : List Nat := [1, 4, 2, 3, 1, 2, 1, 9]
def baseStart_4371741 : Nat := 118140960795 + 4371741 * 2 ^ 59
def prefixEnd_4371741 : Nat := 4983230072969 + 3 ^ 40 * 4371741 * 2
def baseEnd_4371741 : Nat := 83140904813610565812305

theorem tailTrace_4371741 : CollatzResearch.WordTrace tailWord_4371741 prefixEnd_4371741 83140904813610565812305 := by
  unfold tailWord_4371741
  simp only [CollatzResearch.WordTrace]
  refine ⟨159450493654936465765347077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106300329103290977176898051 159450493654936465765347077)
  ·
    refine ⟨29896967560300587331002577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 159450493654936465765347077 29896967560300587331002577)
    ·
      refine ⟨22422725670225440498251933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29896967560300587331002577 22422725670225440498251933)
      ·
        refine ⟨8408522126334540186844475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22422725670225440498251933 8408522126334540186844475)
        ·
          refine ⟨12612783189501810280266713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8408522126334540186844475 12612783189501810280266713)
          ·
            refine ⟨9459587392126357710200035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12612783189501810280266713 9459587392126357710200035)
            ·
              refine ⟨14189381088189536565300053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9459587392126357710200035 14189381088189536565300053)
              ·
                refine ⟨83140904813610565812305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14189381088189536565300053 83140904813610565812305)
                ·
                  rfl

theorem cell23_4371741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 9].length) (baseStart_4371741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4371741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4371741 prefixEnd_4371741 := by exact prefixLift 4371741
  have htrace : WordTrace (prefixWord ++ tailWord_4371741) baseStart_4371741 baseEnd_4371741 := by
    simpa [prefixWord, tailWord_4371741, baseEnd_4371741] using wordTrace_append hprefix tailTrace_4371741
  have hstable : (prefixWord ++ tailWord_4371741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4371741).length < 2 ^ (prefixWord ++ tailWord_4371741).sum := by decide
  have hdescent : baseEnd_4371741 < baseStart_4371741 := by decide
  rcases family_descends (prefixWord ++ tailWord_4371741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4371768 : List Nat := [2, 1, 2, 1, 3, 1, 1, 6, 2, 1, 3]
def baseStart_4371768 : Nat := 118140960795 + 4371768 * 2 ^ 59
def prefixEnd_4371768 : Nat := 4983230072969 + 3 ^ 40 * 4371768 * 2
def baseEnd_4371768 : Nat := 2244818293945156671294611

theorem tailTrace_4371768 : CollatzResearch.WordTrace tailWord_4371768 prefixEnd_4371768 2244818293945156671294611 := by
  unfold tailWord_4371768
  simp only [CollatzResearch.WordTrace]
  refine ⟨79725739212919324688289979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106300985617225766251053305 79725739212919324688289979)
  ·
    refine ⟨119588608819378987032434969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79725739212919324688289979 119588608819378987032434969)
    ·
      refine ⟨89691456614534240274326227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119588608819378987032434969 89691456614534240274326227)
      ·
        refine ⟨134537184921801360411489341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89691456614534240274326227 134537184921801360411489341)
        ·
          refine ⟨50451444345675510154308503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134537184921801360411489341 50451444345675510154308503)
          ·
            refine ⟨75677166518513265231462755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50451444345675510154308503 75677166518513265231462755)
            ·
              refine ⟨113515749777769897847194133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75677166518513265231462755 113515749777769897847194133)
              ·
                refine ⟨5321050770832963961587225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 113515749777769897847194133 5321050770832963961587225)
                ·
                  refine ⟨3990788078124722971190419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5321050770832963961587225 3990788078124722971190419)
                  ·
                    refine ⟨5986182117187084456785629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3990788078124722971190419 5986182117187084456785629)
                    ·
                      refine ⟨2244818293945156671294611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5986182117187084456785629 2244818293945156671294611)
                      ·
                        rfl

theorem cell23_4371768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 6, 2, 1, 3].length) (baseStart_4371768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4371768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4371768 prefixEnd_4371768 := by exact prefixLift 4371768
  have htrace : WordTrace (prefixWord ++ tailWord_4371768) baseStart_4371768 baseEnd_4371768 := by
    simpa [prefixWord, tailWord_4371768, baseEnd_4371768] using wordTrace_append hprefix tailTrace_4371768
  have hstable : (prefixWord ++ tailWord_4371768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4371768).length < 2 ^ (prefixWord ++ tailWord_4371768).sum := by decide
  have hdescent : baseEnd_4371768 < baseStart_4371768 := by decide
  rcases family_descends (prefixWord ++ tailWord_4371768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4371769 : List Nat := [1, 2, 1, 6, 3, 1, 1, 1, 3, 2, 2]
def baseStart_4371769 : Nat := 118140960795 + 4371769 * 2 ^ 59
def prefixEnd_4371769 : Nat := 4983230072969 + 3 ^ 40 * 4371769 * 2
def baseEnd_4371769 : Nat := 2244818807425811167382107

theorem tailTrace_4371769 : CollatzResearch.WordTrace tailWord_4371769 prefixEnd_4371769 2244818807425811167382107 := by
  unfold tailWord_4371769
  simp only [CollatzResearch.WordTrace]
  refine ⟨159451514898835026547366361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106301009932556684364910907 159451514898835026547366361)
  ·
    refine ⟨119588636174126269910524771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159451514898835026547366361 119588636174126269910524771)
    ·
      refine ⟨179382954261189404865787157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119588636174126269910524771 179382954261189404865787157)
      ·
        refine ⟨8408575980993253353083773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 179382954261189404865787157 8408575980993253353083773)
        ·
          refine ⟨3153215992872470007406415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8408575980993253353083773 3153215992872470007406415)
          ·
            refine ⟨4729823989308705011109623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3153215992872470007406415 4729823989308705011109623)
            ·
              refine ⟨7094735983963057516664435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4729823989308705011109623 7094735983963057516664435)
              ·
                refine ⟨10642103975944586274996653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7094735983963057516664435 10642103975944586274996653)
                ·
                  refine ⟨3990788990979219853123745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10642103975944586274996653 3990788990979219853123745)
                  ·
                    refine ⟨2993091743234414889842809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3990788990979219853123745 2993091743234414889842809)
                    ·
                      refine ⟨2244818807425811167382107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2993091743234414889842809 2244818807425811167382107)
                      ·
                        rfl

theorem cell23_4371769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_4371769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4371769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4371769 prefixEnd_4371769 := by exact prefixLift 4371769
  have htrace : WordTrace (prefixWord ++ tailWord_4371769) baseStart_4371769 baseEnd_4371769 := by
    simpa [prefixWord, tailWord_4371769, baseEnd_4371769] using wordTrace_append hprefix tailTrace_4371769
  have hstable : (prefixWord ++ tailWord_4371769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4371769).length < 2 ^ (prefixWord ++ tailWord_4371769).sum := by decide
  have hdescent : baseEnd_4371769 < baseStart_4371769 := by decide
  rcases family_descends (prefixWord ++ tailWord_4371769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4371784 : List Nat := [2, 1, 3, 1, 1, 2, 1, 3, 1, 8]
def baseStart_4371784 : Nat := 118140960795 + 4371784 * 2 ^ 59
def prefixEnd_4371784 : Nat := 4983230072969 + 3 ^ 40 * 4371784 * 2
def baseEnd_4371784 : Nat := 748275503211876202898179

theorem tailTrace_4371784 : CollatzResearch.WordTrace tailWord_4371784 prefixEnd_4371784 748275503211876202898179 := by
  unfold tailWord_4371784
  simp only [CollatzResearch.WordTrace]
  refine ⟨79726030996890342054581203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106301374662520456072774937 79726030996890342054581203)
  ·
    refine ⟨119589046495335513081871805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79726030996890342054581203 119589046495335513081871805)
    ·
      refine ⟨44845892435750817405701927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119589046495335513081871805 44845892435750817405701927)
      ·
        refine ⟨67268838653626226108552891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44845892435750817405701927 67268838653626226108552891)
        ·
          refine ⟨100903257980439339162829337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67268838653626226108552891 100903257980439339162829337)
          ·
            refine ⟨75677443485329504372122003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100903257980439339162829337 75677443485329504372122003)
            ·
              refine ⟨113516165227994256558183005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75677443485329504372122003 113516165227994256558183005)
              ·
                refine ⟨42568561960497846209318627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 113516165227994256558183005 42568561960497846209318627)
                ·
                  refine ⟨63852842940746769313977941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42568561960497846209318627 63852842940746769313977941)
                  ·
                    refine ⟨748275503211876202898179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 63852842940746769313977941 748275503211876202898179)
                    ·
                      rfl

theorem cell23_4371784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 1, 8].length) (baseStart_4371784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4371784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4371784 prefixEnd_4371784 := by exact prefixLift 4371784
  have htrace : WordTrace (prefixWord ++ tailWord_4371784) baseStart_4371784 baseEnd_4371784 := by
    simpa [prefixWord, tailWord_4371784, baseEnd_4371784] using wordTrace_append hprefix tailTrace_4371784
  have hstable : (prefixWord ++ tailWord_4371784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4371784).length < 2 ^ (prefixWord ++ tailWord_4371784).sum := by decide
  have hdescent : baseEnd_4371784 < baseStart_4371784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4371784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4371785 : List Nat := [1, 2, 1, 1, 2, 3, 6, 1, 2, 1, 3]
def baseStart_4371785 : Nat := 118140960795 + 4371785 * 2 ^ 59
def prefixEnd_4371785 : Nat := 4983230072969 + 3 ^ 40 * 4371785 * 2
def baseEnd_4371785 : Nat := 2244827023116283104782033

theorem tailTrace_4371785 : CollatzResearch.WordTrace tailWord_4371785 prefixEnd_4371785 2244827023116283104782033 := by
  unfold tailWord_4371785
  simp only [CollatzResearch.WordTrace]
  refine ⟨159452098466777061279948809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106301398977851374186632539 159452098466777061279948809)
  ·
    refine ⟨119589073850082795959961607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159452098466777061279948809 119589073850082795959961607)
    ·
      refine ⟨179383610775124193939942411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119589073850082795959961607 179383610775124193939942411)
      ·
        refine ⟨269075416162686290909913617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179383610775124193939942411 269075416162686290909913617)
        ·
          refine ⟨201806562122014718182435213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 269075416162686290909913617 201806562122014718182435213)
          ·
            refine ⟨75677460795755519318413205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 201806562122014718182435213 75677460795755519318413205)
            ·
              refine ⟨3547380974801039968050619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 75677460795755519318413205 3547380974801039968050619)
              ·
                refine ⟨5321071462201559952075929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3547380974801039968050619 5321071462201559952075929)
                ·
                  refine ⟨3990803596651169964056947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5321071462201559952075929 3990803596651169964056947)
                  ·
                    refine ⟨5986205394976754946085421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3990803596651169964056947 5986205394976754946085421)
                    ·
                      refine ⟨2244827023116283104782033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5986205394976754946085421 2244827023116283104782033)
                      ·
                        rfl

theorem cell23_4371785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 6, 1, 2, 1, 3].length) (baseStart_4371785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4371785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4371785 prefixEnd_4371785 := by exact prefixLift 4371785
  have htrace : WordTrace (prefixWord ++ tailWord_4371785) baseStart_4371785 baseEnd_4371785 := by
    simpa [prefixWord, tailWord_4371785, baseEnd_4371785] using wordTrace_append hprefix tailTrace_4371785
  have hstable : (prefixWord ++ tailWord_4371785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4371785).length < 2 ^ (prefixWord ++ tailWord_4371785).sum := by decide
  have hdescent : baseEnd_4371785 < baseStart_4371785 := by decide
  rcases family_descends (prefixWord ++ tailWord_4371785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4371789 : List Nat := [1, 6, 1, 3, 1, 2, 1, 2, 1, 2, 3]
def baseStart_4371789 : Nat := 118140960795 + 4371789 * 2 ^ 59
def prefixEnd_4371789 : Nat := 4983230072969 + 3 ^ 40 * 4371789 * 2
def baseEnd_4371789 : Nat := 2244829077038901089132015

theorem tailTrace_4371789 : CollatzResearch.WordTrace tailWord_4371789 prefixEnd_4371789 2244829077038901089132015 := by
  unfold tailWord_4371789
  simp only [CollatzResearch.WordTrace]
  refine ⟨159452244358762569963094421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106301496239175046642062947 159452244358762569963094421)
  ·
    refine ⟨7474323954316995467020051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 159452244358762569963094421 7474323954316995467020051)
    ·
      refine ⟨11211485931475493200530077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7474323954316995467020051 11211485931475493200530077)
      ·
        refine ⟨4204307224303309950198779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11211485931475493200530077 4204307224303309950198779)
        ·
          refine ⟨6306460836454964925298169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4204307224303309950198779 6306460836454964925298169)
          ·
            refine ⟨4729845627341223693973627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6306460836454964925298169 4729845627341223693973627)
            ·
              refine ⟨7094768441011835540960441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4729845627341223693973627 7094768441011835540960441)
              ·
                refine ⟨5321076330758876655720331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7094768441011835540960441 5321076330758876655720331)
                ·
                  refine ⟨7981614496138314983580497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5321076330758876655720331 7981614496138314983580497)
                  ·
                    refine ⟨5986210872103736237685373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7981614496138314983580497 5986210872103736237685373)
                    ·
                      refine ⟨2244829077038901089132015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5986210872103736237685373 2244829077038901089132015)
                      ·
                        rfl

theorem cell23_4371789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_4371789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4371789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4371789 prefixEnd_4371789 := by exact prefixLift 4371789
  have htrace : WordTrace (prefixWord ++ tailWord_4371789) baseStart_4371789 baseEnd_4371789 := by
    simpa [prefixWord, tailWord_4371789, baseEnd_4371789] using wordTrace_append hprefix tailTrace_4371789
  have hstable : (prefixWord ++ tailWord_4371789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4371789).length < 2 ^ (prefixWord ++ tailWord_4371789).sum := by decide
  have hdescent : baseEnd_4371789 < baseStart_4371789 := by decide
  rcases family_descends (prefixWord ++ tailWord_4371789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4371808 : List Nat := [2, 1, 1, 3, 4, 1, 1, 1, 3, 4, 2]
def baseStart_4371808 : Nat := 118140960795 + 4371808 * 2 ^ 59
def prefixEnd_4371808 : Nat := 4983230072969 + 3 ^ 40 * 4371808 * 2
def baseEnd_4371808 : Nat := 2244838833171336514794427

theorem tailTrace_4371808 : CollatzResearch.WordTrace tailWord_4371808 prefixEnd_4371808 2244838833171336514794427 := by
  unfold tailWord_4371808
  simp only [CollatzResearch.WordTrace]
  refine ⟨79726468672846868104018039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106301958230462490805357385 79726468672846868104018039)
  ·
    refine ⟨119589703009270302156027059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79726468672846868104018039 119589703009270302156027059)
    ·
      refine ⟨179384554513905453234040589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119589703009270302156027059 179384554513905453234040589)
      ·
        refine ⟨67269207942714544962765221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 179384554513905453234040589 67269207942714544962765221)
        ·
          refine ⟨12612976489258977180518479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67269207942714544962765221 12612976489258977180518479)
          ·
            refine ⟨18919464733888465770777719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12612976489258977180518479 18919464733888465770777719)
            ·
              refine ⟨28379197100832698656166579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18919464733888465770777719 28379197100832698656166579)
              ·
                refine ⟨42568795651249047984249869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28379197100832698656166579 42568795651249047984249869)
                ·
                  refine ⟨15963298369218392994093701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42568795651249047984249869 15963298369218392994093701)
                  ·
                    refine ⟨2993118444228448686392569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15963298369218392994093701 2993118444228448686392569)
                    ·
                      refine ⟨2244838833171336514794427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2993118444228448686392569 2244838833171336514794427)
                      ·
                        rfl

theorem cell23_4371808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 3, 4, 2].length) (baseStart_4371808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4371808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4371808 prefixEnd_4371808 := by exact prefixLift 4371808
  have htrace : WordTrace (prefixWord ++ tailWord_4371808) baseStart_4371808 baseEnd_4371808 := by
    simpa [prefixWord, tailWord_4371808, baseEnd_4371808] using wordTrace_append hprefix tailTrace_4371808
  have hstable : (prefixWord ++ tailWord_4371808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4371808).length < 2 ^ (prefixWord ++ tailWord_4371808).sum := by decide
  have hdescent : baseEnd_4371808 < baseStart_4371808 := by decide
  rcases family_descends (prefixWord ++ tailWord_4371808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4371811 : List Nat := [1, 1, 1, 5, 2, 2, 2, 1, 2, 1, 5]
def baseStart_4371811 : Nat := 118140960795 + 4371811 * 2 ^ 59
def prefixEnd_4371811 : Nat := 4983230072969 + 3 ^ 40 * 4371811 * 2
def baseEnd_4371811 : Nat := 2244840373613300003056913

theorem tailTrace_4371811 : CollatzResearch.WordTrace tailWord_4371811 prefixEnd_4371811 2244840373613300003056913 := by
  unfold tailWord_4371811
  simp only [CollatzResearch.WordTrace]
  refine ⟨159453046764682867720395287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106302031176455245146930191 159453046764682867720395287)
  ·
    refine ⟨239179570147024301580592931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159453046764682867720395287 239179570147024301580592931)
    ·
      refine ⟨358769355220536452370889397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239179570147024301580592931 358769355220536452370889397)
      ·
        refine ⟨33634627051925292409770881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 358769355220536452370889397 33634627051925292409770881)
        ·
          refine ⟨25225970288943969307328161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33634627051925292409770881 25225970288943969307328161)
          ·
            refine ⟨18919477716707976980496121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25225970288943969307328161 18919477716707976980496121)
            ·
              refine ⟨14189608287530982735372091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18919477716707976980496121 14189608287530982735372091)
              ·
                refine ⟨21284412431296474103058137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14189608287530982735372091 21284412431296474103058137)
                ·
                  refine ⟨15963309323472355577293603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21284412431296474103058137 15963309323472355577293603)
                  ·
                    refine ⟨23944963985208533365940405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15963309323472355577293603 23944963985208533365940405)
                    ·
                      refine ⟨2244840373613300003056913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23944963985208533365940405 2244840373613300003056913)
                      ·
                        rfl

theorem cell23_4371811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_4371811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4371811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4371811 prefixEnd_4371811 := by exact prefixLift 4371811
  have htrace : WordTrace (prefixWord ++ tailWord_4371811) baseStart_4371811 baseEnd_4371811 := by
    simpa [prefixWord, tailWord_4371811, baseEnd_4371811] using wordTrace_append hprefix tailTrace_4371811
  have hstable : (prefixWord ++ tailWord_4371811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4371811).length < 2 ^ (prefixWord ++ tailWord_4371811).sum := by decide
  have hdescent : baseEnd_4371811 < baseStart_4371811 := by decide
  rcases family_descends (prefixWord ++ tailWord_4371811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4371812 : List Nat := [2, 3, 1, 1, 3, 3, 3, 1, 1, 3, 2]
def baseStart_4371812 : Nat := 118140960795 + 4371812 * 2 ^ 59
def prefixEnd_4371812 : Nat := 4983230072969 + 3 ^ 40 * 4371812 * 2
def baseEnd_4371812 : Nat := 2244840887093954499144409

theorem tailTrace_4371812 : CollatzResearch.WordTrace tailWord_4371812 prefixEnd_4371812 2244840887093954499144409 := by
  unfold tailWord_4371812
  simp only [CollatzResearch.WordTrace]
  refine ⟨79726541618839622445590845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106302055491786163260787793 79726541618839622445590845)
  ·
    refine ⟨29897453107064858417096567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79726541618839622445590845 29897453107064858417096567)
    ·
      refine ⟨44846179660597287625644851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29897453107064858417096567 44846179660597287625644851)
      ·
        refine ⟨67269269490895931438467277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44846179660597287625644851 67269269490895931438467277)
        ·
          refine ⟨25225976059085974289425229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67269269490895931438467277 25225976059085974289425229)
          ·
            refine ⟨9459741022157240358534461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25225976059085974289425229 9459741022157240358534461)
            ·
              refine ⟨3547402883308965134450423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9459741022157240358534461 3547402883308965134450423)
              ·
                refine ⟨5321104324963447701675635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3547402883308965134450423 5321104324963447701675635)
                ·
                  refine ⟨7981656487445171552513453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5321104324963447701675635 7981656487445171552513453)
                  ·
                    refine ⟨2993121182791939332192545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7981656487445171552513453 2993121182791939332192545)
                    ·
                      refine ⟨2244840887093954499144409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2993121182791939332192545 2244840887093954499144409)
                      ·
                        rfl

theorem cell23_4371812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 3, 1, 1, 3, 2].length) (baseStart_4371812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4371812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4371812 prefixEnd_4371812 := by exact prefixLift 4371812
  have htrace : WordTrace (prefixWord ++ tailWord_4371812) baseStart_4371812 baseEnd_4371812 := by
    simpa [prefixWord, tailWord_4371812, baseEnd_4371812] using wordTrace_append hprefix tailTrace_4371812
  have hstable : (prefixWord ++ tailWord_4371812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4371812).length < 2 ^ (prefixWord ++ tailWord_4371812).sum := by decide
  have hdescent : baseEnd_4371812 < baseStart_4371812 := by decide
  rcases family_descends (prefixWord ++ tailWord_4371812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4371825 : List Nat := [1, 2, 2, 2, 1, 2, 3, 4, 2, 2, 2]
def baseStart_4371825 : Nat := 118140960795 + 4371825 * 2 ^ 59
def prefixEnd_4371825 : Nat := 4983230072969 + 3 ^ 40 * 4371825 * 2
def baseEnd_4371825 : Nat := 2244847562342462948281849

theorem tailTrace_4371825 : CollatzResearch.WordTrace tailWord_4371825 prefixEnd_4371825 2244847562342462948281849 := by
  unfold tailWord_4371825
  simp only [CollatzResearch.WordTrace]
  refine ⟨159453557386632148111404929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106302371591088098740936619 159453557386632148111404929)
  ·
    refine ⟨119590168039974111083553697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159453557386632148111404929 119590168039974111083553697)
    ·
      refine ⟨89692626029980583312665273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119590168039974111083553697 89692626029980583312665273)
      ·
        refine ⟨67269469522485437484498955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89692626029980583312665273 67269469522485437484498955)
        ·
          refine ⟨100904204283728156226748433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67269469522485437484498955 100904204283728156226748433)
          ·
            refine ⟨75678153212796117170061325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100904204283728156226748433 75678153212796117170061325)
            ·
              refine ⟨28379307454798543938772997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75678153212796117170061325 28379307454798543938772997)
              ·
                refine ⟨5321120147774726988519937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28379307454798543938772997 5321120147774726988519937)
                ·
                  refine ⟨3990840110831045241389953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5321120147774726988519937 3990840110831045241389953)
                  ·
                    refine ⟨2993130083123283931042465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3990840110831045241389953 2993130083123283931042465)
                    ·
                      refine ⟨2244847562342462948281849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2993130083123283931042465 2244847562342462948281849)
                      ·
                        rfl

theorem cell23_4371825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 4, 2, 2, 2].length) (baseStart_4371825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4371825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4371825 prefixEnd_4371825 := by exact prefixLift 4371825
  have htrace : WordTrace (prefixWord ++ tailWord_4371825) baseStart_4371825 baseEnd_4371825 := by
    simpa [prefixWord, tailWord_4371825, baseEnd_4371825] using wordTrace_append hprefix tailTrace_4371825
  have hstable : (prefixWord ++ tailWord_4371825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4371825).length < 2 ^ (prefixWord ++ tailWord_4371825).sum := by decide
  have hdescent : baseEnd_4371825 < baseStart_4371825 := by decide
  rcases family_descends (prefixWord ++ tailWord_4371825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4371842 : List Nat := [3, 4, 2, 1, 1, 1, 1, 3, 1, 4, 2]
def baseStart_4371842 : Nat := 118140960795 + 4371842 * 2 ^ 59
def prefixEnd_4371842 : Nat := 4983230072969 + 3 ^ 40 * 4371842 * 2
def baseEnd_4371842 : Nat := 2244856291513589381769271

theorem tailTrace_4371842 : CollatzResearch.WordTrace tailWord_4371842 prefixEnd_4371842 2244856291513589381769271 := by
  unfold tailWord_4371842
  simp only [CollatzResearch.WordTrace]
  refine ⟨39863544356892640003693445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106302784951713706676515853 39863544356892640003693445)
  ·
    refine ⟨7474414566917370000692521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39863544356892640003693445 7474414566917370000692521)
    ·
      refine ⟨5605810925188027500519391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7474414566917370000692521 5605810925188027500519391)
      ·
        refine ⟨8408716387782041250779087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5605810925188027500519391 8408716387782041250779087)
        ·
          refine ⟨12613074581673061876168631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8408716387782041250779087 12613074581673061876168631)
          ·
            refine ⟨18919611872509592814252947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12613074581673061876168631 18919611872509592814252947)
            ·
              refine ⟨28379417808764389221379421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18919611872509592814252947 28379417808764389221379421)
              ·
                refine ⟨10642281678286645958017283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28379417808764389221379421 10642281678286645958017283)
                ·
                  refine ⟨15963422517429968937025925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10642281678286645958017283 15963422517429968937025925)
                  ·
                    refine ⟨2993141722018119175692361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15963422517429968937025925 2993141722018119175692361)
                    ·
                      refine ⟨2244856291513589381769271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2993141722018119175692361 2244856291513589381769271)
                      ·
                        rfl

theorem cell23_4371842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_4371842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4371842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4371842 prefixEnd_4371842 := by exact prefixLift 4371842
  have htrace : WordTrace (prefixWord ++ tailWord_4371842) baseStart_4371842 baseEnd_4371842 := by
    simpa [prefixWord, tailWord_4371842, baseEnd_4371842] using wordTrace_append hprefix tailTrace_4371842
  have hstable : (prefixWord ++ tailWord_4371842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4371842).length < 2 ^ (prefixWord ++ tailWord_4371842).sum := by decide
  have hdescent : baseEnd_4371842 < baseStart_4371842 := by decide
  rcases family_descends (prefixWord ++ tailWord_4371842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4371911 : List Nat := [1, 1, 4, 1, 1, 3, 1, 1, 2, 4, 4]
def baseStart_4371911 : Nat := 118140960795 + 4371911 * 2 ^ 59
def prefixEnd_4371911 : Nat := 4983230072969 + 3 ^ 40 * 4371911 * 2
def baseEnd_4371911 : Nat := 2244891721678749611806453

theorem tailTrace_4371911 : CollatzResearch.WordTrace tailWord_4371911 prefixEnd_4371911 2244891721678749611806453 := by
  unfold tailWord_4371911
  simp only [CollatzResearch.WordTrace]
  refine ⟨159456694064320584799035587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106304462709547056532690391 159456694064320584799035587)
  ·
    refine ⟨239185041096480877198553381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159456694064320584799035587 239185041096480877198553381)
    ·
      refine ⟨44847195205590164474728759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 239185041096480877198553381 44847195205590164474728759)
      ·
        refine ⟨67270792808385246712093139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44847195205590164474728759 67270792808385246712093139)
        ·
          refine ⟨100906189212577870068139709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67270792808385246712093139 100906189212577870068139709)
          ·
            refine ⟨37839820954716701275552391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100906189212577870068139709 37839820954716701275552391)
            ·
              refine ⟨56759731432075051913328587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37839820954716701275552391 56759731432075051913328587)
              ·
                refine ⟨85139597148112577869992881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56759731432075051913328587 85139597148112577869992881)
                ·
                  refine ⟨63854697861084433402494661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85139597148112577869992881 63854697861084433402494661)
                  ·
                    refine ⟨11972755848953331262967749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 63854697861084433402494661 11972755848953331262967749)
                    ·
                      refine ⟨2244891721678749611806453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11972755848953331262967749 2244891721678749611806453)
                      ·
                        rfl

theorem cell23_4371911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 4, 4].length) (baseStart_4371911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4371911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4371911 prefixEnd_4371911 := by exact prefixLift 4371911
  have htrace : WordTrace (prefixWord ++ tailWord_4371911) baseStart_4371911 baseEnd_4371911 := by
    simpa [prefixWord, tailWord_4371911, baseEnd_4371911] using wordTrace_append hprefix tailTrace_4371911
  have hstable : (prefixWord ++ tailWord_4371911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4371911).length < 2 ^ (prefixWord ++ tailWord_4371911).sum := by decide
  have hdescent : baseEnd_4371911 < baseStart_4371911 := by decide
  rcases family_descends (prefixWord ++ tailWord_4371911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4371918 : List Nat := [4, 1, 1, 1, 2, 1, 4, 1, 1, 4, 3]
def baseStart_4371918 : Nat := 118140960795 + 4371918 * 2 ^ 59
def prefixEnd_4371918 : Nat := 4983230072969 + 3 ^ 40 * 4371918 * 2
def baseEnd_4371918 : Nat := 2244895316043331084418921

theorem tailTrace_4371918 : CollatzResearch.WordTrace tailWord_4371918 prefixEnd_4371918 2244895316043331084418921 := by
  unfold tailWord_4371918
  simp only [CollatzResearch.WordTrace]
  refine ⟨19932118671911903124317551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106304632916863483329693605 19932118671911903124317551)
  ·
    refine ⟨29898178007867854686476327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19932118671911903124317551 29898178007867854686476327)
    ·
      refine ⟨44847267011801782029714491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29898178007867854686476327 44847267011801782029714491)
      ·
        refine ⟨67270900517702673044571737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44847267011801782029714491 67270900517702673044571737)
        ·
          refine ⟨50453175388277004783428803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67270900517702673044571737 50453175388277004783428803)
          ·
            refine ⟨75679763082415507175143205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50453175388277004783428803 75679763082415507175143205)
            ·
              refine ⟨14189955577952907595339351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75679763082415507175143205 14189955577952907595339351)
              ·
                refine ⟨21284933366929361393009027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14189955577952907595339351 21284933366929361393009027)
                ·
                  refine ⟨31927400050394042089513541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21284933366929361393009027 31927400050394042089513541)
                  ·
                    refine ⟨5986387509448882891783789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31927400050394042089513541 5986387509448882891783789)
                    ·
                      refine ⟨2244895316043331084418921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5986387509448882891783789 2244895316043331084418921)
                      ·
                        rfl

theorem cell23_4371918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 1, 4, 3].length) (baseStart_4371918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4371918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4371918 prefixEnd_4371918 := by exact prefixLift 4371918
  have htrace : WordTrace (prefixWord ++ tailWord_4371918) baseStart_4371918 baseEnd_4371918 := by
    simpa [prefixWord, tailWord_4371918, baseEnd_4371918] using wordTrace_append hprefix tailTrace_4371918
  have hstable : (prefixWord ++ tailWord_4371918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4371918).length < 2 ^ (prefixWord ++ tailWord_4371918).sum := by decide
  have hdescent : baseEnd_4371918 < baseStart_4371918 := by decide
  rcases family_descends (prefixWord ++ tailWord_4371918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4371985 : List Nat := [1, 2, 2, 1, 1, 2, 7, 1, 1, 5]
def baseStart_4371985 : Nat := 118140960795 + 4371985 * 2 ^ 59
def prefixEnd_4371985 : Nat := 4983230072969 + 3 ^ 40 * 4371985 * 2
def baseEnd_4371985 : Nat := 748309906415727440760371

theorem tailTrace_4371985 : CollatzResearch.WordTrace tailWord_4371985 prefixEnd_4371985 748309906415727440760371 := by
  unfold tailWord_4371985
  simp only [CollatzResearch.WordTrace]
  refine ⟨159459393066052495437229409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106306262044034996958152939 159459393066052495437229409)
  ·
    refine ⟨119594544799539371577922057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159459393066052495437229409 119594544799539371577922057)
    ·
      refine ⟨89695908599654528683441543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119594544799539371577922057 89695908599654528683441543)
      ·
        refine ⟨134543862899481793025162315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89695908599654528683441543 134543862899481793025162315)
        ·
          refine ⟨201815794349222689537743473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134543862899481793025162315 201815794349222689537743473)
          ·
            refine ⟨151361845761917017153307605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 201815794349222689537743473 151361845761917017153307605)
            ·
              refine ⟨3547543260044930089530647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 151361845761917017153307605 3547543260044930089530647)
              ·
                refine ⟨5321314890067395134295971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3547543260044930089530647 5321314890067395134295971)
                ·
                  refine ⟨7981972335101092701443957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5321314890067395134295971 7981972335101092701443957)
                  ·
                    refine ⟨748309906415727440760371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7981972335101092701443957 748309906415727440760371)
                    ·
                      rfl

theorem cell23_4371985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 7, 1, 1, 5].length) (baseStart_4371985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4371985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4371985 prefixEnd_4371985 := by exact prefixLift 4371985
  have htrace : WordTrace (prefixWord ++ tailWord_4371985) baseStart_4371985 baseEnd_4371985 := by
    simpa [prefixWord, tailWord_4371985, baseEnd_4371985] using wordTrace_append hprefix tailTrace_4371985
  have hstable : (prefixWord ++ tailWord_4371985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4371985).length < 2 ^ (prefixWord ++ tailWord_4371985).sum := by decide
  have hdescent : baseEnd_4371985 < baseStart_4371985 := by decide
  rcases family_descends (prefixWord ++ tailWord_4371985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4371999 : List Nat := [1, 1, 2, 4, 1, 1, 6, 2, 1, 1, 3]
def baseStart_4371999 : Nat := 118140960795 + 4371999 * 2 ^ 59
def prefixEnd_4371999 : Nat := 4983230072969 + 3 ^ 40 * 4371999 * 2
def baseEnd_4371999 : Nat := 2244936907976345267506049

theorem tailTrace_4371999 : CollatzResearch.WordTrace tailWord_4371999 prefixEnd_4371999 2244936907976345267506049 := by
  unfold tailWord_4371999
  simp only [CollatzResearch.WordTrace]
  refine ⟨159459903688001775828239051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106306602458667850552159367 159459903688001775828239051)
  ·
    refine ⟨239189855532002663742358577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159459903688001775828239051 239189855532002663742358577)
    ·
      refine ⟨179392391649001997806768933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 239189855532002663742358577 179392391649001997806768933)
      ·
        refine ⟨33636073434187874588769175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 179392391649001997806768933 33636073434187874588769175)
        ·
          refine ⟨50454110151281811883153763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33636073434187874588769175 50454110151281811883153763)
          ·
            refine ⟨75681165226922717824730645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50454110151281811883153763 75681165226922717824730645)
            ·
              refine ⟨3547554620012002398034249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 75681165226922717824730645 3547554620012002398034249)
              ·
                refine ⟨2660665965009001798525687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3547554620012002398034249 2660665965009001798525687)
                ·
                  refine ⟨3990998947513502697788531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2660665965009001798525687 3990998947513502697788531)
                  ·
                    refine ⟨5986498421270254046682797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3990998947513502697788531 5986498421270254046682797)
                    ·
                      refine ⟨2244936907976345267506049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5986498421270254046682797 2244936907976345267506049)
                      ·
                        rfl

theorem cell23_4371999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 6, 2, 1, 1, 3].length) (baseStart_4371999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4371999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4371999 prefixEnd_4371999 := by exact prefixLift 4371999
  have htrace : WordTrace (prefixWord ++ tailWord_4371999) baseStart_4371999 baseEnd_4371999 := by
    simpa [prefixWord, tailWord_4371999, baseEnd_4371999] using wordTrace_append hprefix tailTrace_4371999
  have hstable : (prefixWord ++ tailWord_4371999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4371999).length < 2 ^ (prefixWord ++ tailWord_4371999).sum := by decide
  have hdescent : baseEnd_4371999 < baseStart_4371999 := by decide
  rcases family_descends (prefixWord ++ tailWord_4371999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4372025 : List Nat := [1, 2, 1, 5, 1, 2, 2, 1, 3, 2, 3]
def baseStart_4372025 : Nat := 118140960795 + 4372025 * 2 ^ 59
def prefixEnd_4372025 : Nat := 4983230072969 + 3 ^ 40 * 4372025 * 2
def baseEnd_4372025 : Nat := 2244950258473362165780929

theorem tailTrace_4372025 : CollatzResearch.WordTrace tailWord_4372025 prefixEnd_4372025 2244950258473362165780929 := by
  unfold tailWord_4372025
  simp only [CollatzResearch.WordTrace]
  refine ⟨159460851985907582268685529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106307234657271721512457019 159460851985907582268685529)
  ·
    refine ⟨119595638989430686701514147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159460851985907582268685529 119595638989430686701514147)
    ·
      refine ⟨179393458484146030052271221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119595638989430686701514147 179393458484146030052271221)
      ·
        refine ⟨16818136732888690317400427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 179393458484146030052271221 16818136732888690317400427)
        ·
          refine ⟨25227205099333035476100641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16818136732888690317400427 25227205099333035476100641)
          ·
            refine ⟨18920403824499776607075481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25227205099333035476100641 18920403824499776607075481)
            ·
              refine ⟨14190302868374832455306611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18920403824499776607075481 14190302868374832455306611)
              ·
                refine ⟨21285454302562248682959917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14190302868374832455306611 21285454302562248682959917)
                ·
                  refine ⟨7982045363460843256109969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21285454302562248682959917 7982045363460843256109969)
                  ·
                    refine ⟨5986534022595632442082477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7982045363460843256109969 5986534022595632442082477)
                    ·
                      refine ⟨2244950258473362165780929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5986534022595632442082477 2244950258473362165780929)
                      ·
                        rfl

theorem cell23_4372025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_4372025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4372025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4372025 prefixEnd_4372025 := by exact prefixLift 4372025
  have htrace : WordTrace (prefixWord ++ tailWord_4372025) baseStart_4372025 baseEnd_4372025 := by
    simpa [prefixWord, tailWord_4372025, baseEnd_4372025] using wordTrace_append hprefix tailTrace_4372025
  have hstable : (prefixWord ++ tailWord_4372025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4372025).length < 2 ^ (prefixWord ++ tailWord_4372025).sum := by decide
  have hdescent : baseEnd_4372025 < baseStart_4372025 := by decide
  rcases family_descends (prefixWord ++ tailWord_4372025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4372039 : List Nat := [1, 1, 4, 1, 5, 2, 2, 1, 1, 1, 4]
def baseStart_4372039 : Nat := 118140960795 + 4372039 * 2 ^ 59
def prefixEnd_4372039 : Nat := 4983230072969 + 3 ^ 40 * 4372039 * 2
def baseEnd_4372039 : Nat := 2244957447202525111005865

theorem tailTrace_4372039 : CollatzResearch.WordTrace tailWord_4372039 prefixEnd_4372039 2244957447202525111005865 := by
  unfold tailWord_4372039
  simp only [CollatzResearch.WordTrace]
  refine ⟨159461362607856862659695171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106307575071904575106463447 159461362607856862659695171)
  ·
    refine ⟨239192043911785293989542757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159461362607856862659695171 239192043911785293989542757)
    ·
      refine ⟨44848508233459742623039267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 239192043911785293989542757 44848508233459742623039267)
      ·
        refine ⟨67272762350189613934558901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44848508233459742623039267 67272762350189613934558901)
        ·
          refine ⟨6306821470330276306364897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 67272762350189613934558901 6306821470330276306364897)
          ·
            refine ⟨4730116102747707229773673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6306821470330276306364897 4730116102747707229773673)
            ·
              refine ⟨3547587077060780422330255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4730116102747707229773673 3547587077060780422330255)
              ·
                refine ⟨5321380615591170633495383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3547587077060780422330255 5321380615591170633495383)
                ·
                  refine ⟨7982070923386755950243075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5321380615591170633495383 7982070923386755950243075)
                  ·
                    refine ⟨11973106385080133925364613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7982070923386755950243075 11973106385080133925364613)
                    ·
                      refine ⟨2244957447202525111005865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11973106385080133925364613 2244957447202525111005865)
                      ·
                        rfl

theorem cell23_4372039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 2, 1, 1, 1, 4].length) (baseStart_4372039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4372039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4372039 prefixEnd_4372039 := by exact prefixLift 4372039
  have htrace : WordTrace (prefixWord ++ tailWord_4372039) baseStart_4372039 baseEnd_4372039 := by
    simpa [prefixWord, tailWord_4372039, baseEnd_4372039] using wordTrace_append hprefix tailTrace_4372039
  have hstable : (prefixWord ++ tailWord_4372039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4372039).length < 2 ^ (prefixWord ++ tailWord_4372039).sum := by decide
  have hdescent : baseEnd_4372039 < baseStart_4372039 := by decide
  rcases family_descends (prefixWord ++ tailWord_4372039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4372045 : List Nat := [1, 6, 1, 1, 3, 1, 10]
def baseStart_4372045 : Nat := 118140960795 + 4372045 * 2 ^ 59
def prefixEnd_4372045 : Nat := 4983230072969 + 3 ^ 40 * 4372045 * 2
def baseEnd_4372045 : Nat := 27715562075141383796677

theorem tailTrace_4372045 : CollatzResearch.WordTrace tailWord_4372045 prefixEnd_4372045 27715562075141383796677 := by
  unfold tailWord_4372045
  simp only [CollatzResearch.WordTrace]
  refine ⟨159461581445835125684413589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106307720963890083789609059 159461581445835125684413589)
  ·
    refine ⟨7474761630273521516456887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 159461581445835125684413589 7474761630273521516456887)
    ·
      refine ⟨11212142445410282274685331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7474761630273521516456887 11212142445410282274685331)
      ·
        refine ⟨16818213668115423412027997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11212142445410282274685331 16818213668115423412027997)
        ·
          refine ⟨6306830125543283779510499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16818213668115423412027997 6306830125543283779510499)
          ·
            refine ⟨9460245188314925669265749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6306830125543283779510499 9460245188314925669265749)
            ·
              refine ⟨27715562075141383796677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9460245188314925669265749 27715562075141383796677)
              ·
                rfl

theorem cell23_4372045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 10].length) (baseStart_4372045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4372045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4372045 prefixEnd_4372045 := by exact prefixLift 4372045
  have htrace : WordTrace (prefixWord ++ tailWord_4372045) baseStart_4372045 baseEnd_4372045 := by
    simpa [prefixWord, tailWord_4372045, baseEnd_4372045] using wordTrace_append hprefix tailTrace_4372045
  have hstable : (prefixWord ++ tailWord_4372045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4372045).length < 2 ^ (prefixWord ++ tailWord_4372045).sum := by decide
  have hdescent : baseEnd_4372045 < baseStart_4372045 := by decide
  rcases family_descends (prefixWord ++ tailWord_4372045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4372072 : List Nat := [2, 1, 4, 3, 1, 1, 3, 1, 1, 3, 3]
def baseStart_4372072 : Nat := 118140960795 + 4372072 * 2 ^ 59
def prefixEnd_4372072 : Nat := 4983230072969 + 3 ^ 40 * 4372072 * 2
def baseEnd_4372072 : Nat := 2244974392064123481893213

theorem tailTrace_4372072 : CollatzResearch.WordTrace tailWord_4372072 prefixEnd_4372072 2244974392064123481893213 := by
  unfold tailWord_4372072
  simp only [CollatzResearch.WordTrace]
  refine ⟨79731283108368654647823235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106308377477824872863764313 79731283108368654647823235)
  ·
    refine ⟨119596924662552981971734853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79731283108368654647823235 119596924662552981971734853)
    ·
      refine ⟨22424423374228684119700285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 119596924662552981971734853 22424423374228684119700285)
      ·
        refine ⟨8409158765335756544887607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22424423374228684119700285 8409158765335756544887607)
        ·
          refine ⟨12613738148003634817331411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8409158765335756544887607 12613738148003634817331411)
          ·
            refine ⟨18920607222005452225997117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12613738148003634817331411 18920607222005452225997117)
            ·
              refine ⟨7095227708252044584748919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18920607222005452225997117 7095227708252044584748919)
              ·
                refine ⟨10642841562378066877123379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7095227708252044584748919 10642841562378066877123379)
                ·
                  refine ⟨15964262343567100315685069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10642841562378066877123379 15964262343567100315685069)
                  ·
                    refine ⟨5986598378837662618381901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15964262343567100315685069 5986598378837662618381901)
                    ·
                      refine ⟨2244974392064123481893213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5986598378837662618381901 2244974392064123481893213)
                      ·
                        rfl

theorem cell23_4372072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_4372072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4372072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4372072 prefixEnd_4372072 := by exact prefixLift 4372072
  have htrace : WordTrace (prefixWord ++ tailWord_4372072) baseStart_4372072 baseEnd_4372072 := by
    simpa [prefixWord, tailWord_4372072, baseEnd_4372072] using wordTrace_append hprefix tailTrace_4372072
  have hstable : (prefixWord ++ tailWord_4372072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4372072).length < 2 ^ (prefixWord ++ tailWord_4372072).sum := by decide
  have hdescent : baseEnd_4372072 < baseStart_4372072 := by decide
  rcases family_descends (prefixWord ++ tailWord_4372072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4372085 : List Nat := [1, 3, 4, 2, 1, 1, 1, 1, 2, 2, 5]
def baseStart_4372085 : Nat := 118140960795 + 4372085 * 2 ^ 59
def prefixEnd_4372085 : Nat := 4983230072969 + 3 ^ 40 * 4372085 * 2
def baseEnd_4372085 : Nat := 2244981067312631931030653

theorem tailTrace_4372085 : CollatzResearch.WordTrace tailWord_4372085 prefixEnd_4372085 2244981067312631931030653 := by
  unfold tailWord_4372085
  simp only [CollatzResearch.WordTrace]
  refine ⟨159463040365690212515869709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106308693577126808343913139 159463040365690212515869709)
  ·
    refine ⟨59798640137133829693451141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159463040365690212515869709 59798640137133829693451141)
    ·
      refine ⟨11212245025712593067522089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59798640137133829693451141 11212245025712593067522089)
      ·
        refine ⟨8409183769284444800641567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11212245025712593067522089 8409183769284444800641567)
        ·
          refine ⟨12613775653926667200962351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8409183769284444800641567 12613775653926667200962351)
          ·
            refine ⟨18920663480890000801443527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12613775653926667200962351 18920663480890000801443527)
            ·
              refine ⟨28380995221335001202165291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18920663480890000801443527 28380995221335001202165291)
              ·
                refine ⟨42571492832002501803247937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28380995221335001202165291 42571492832002501803247937)
                ·
                  refine ⟨31928619624001876352435953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42571492832002501803247937 31928619624001876352435953)
                  ·
                    refine ⟨23946464718001407264326965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31928619624001876352435953 23946464718001407264326965)
                    ·
                      refine ⟨2244981067312631931030653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23946464718001407264326965 2244981067312631931030653)
                      ·
                        rfl

theorem cell23_4372085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_4372085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4372085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4372085 prefixEnd_4372085 := by exact prefixLift 4372085
  have htrace : WordTrace (prefixWord ++ tailWord_4372085) baseStart_4372085 baseEnd_4372085 := by
    simpa [prefixWord, tailWord_4372085, baseEnd_4372085] using wordTrace_append hprefix tailTrace_4372085
  have hstable : (prefixWord ++ tailWord_4372085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4372085).length < 2 ^ (prefixWord ++ tailWord_4372085).sum := by decide
  have hdescent : baseEnd_4372085 < baseStart_4372085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4372085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4372155 : List Nat := [1, 1, 1, 1, 1, 2, 3, 2, 4, 5, 2]
def baseStart_4372155 : Nat := 118140960795 + 4372155 * 2 ^ 59
def prefixEnd_4372155 : Nat := 4983230072969 + 3 ^ 40 * 4372155 * 2
def baseEnd_4372155 : Nat := 2245017010958446657155331

theorem tailTrace_4372155 : CollatzResearch.WordTrace tailWord_4372155 prefixEnd_4372155 2245017010958446657155331 := by
  unfold tailWord_4372155
  simp only [CollatzResearch.WordTrace]
  refine ⟨159465593475436614470917919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106310395650291076313945279 159465593475436614470917919)
  ·
    refine ⟨239198390213154921706376879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159465593475436614470917919 239198390213154921706376879)
    ·
      refine ⟨358797585319732382559565319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239198390213154921706376879 358797585319732382559565319)
      ·
        refine ⟨538196377979598573839347979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 358797585319732382559565319 538196377979598573839347979)
        ·
          refine ⟨807294566969397860759021969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 538196377979598573839347979 807294566969397860759021969)
          ·
            refine ⟨605470925227048395569266477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 807294566969397860759021969 605470925227048395569266477)
            ·
              refine ⟨227051596960143148338474929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 605470925227048395569266477 227051596960143148338474929)
              ·
                refine ⟨170288697720107361253856197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 227051596960143148338474929 170288697720107361253856197)
                ·
                  refine ⟨31929130822520130235098037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 170288697720107361253856197 31929130822520130235098037)
                  ·
                    refine ⟨2993356014611262209540441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31929130822520130235098037 2993356014611262209540441)
                    ·
                      refine ⟨2245017010958446657155331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2993356014611262209540441 2245017010958446657155331)
                      ·
                        rfl

theorem cell23_4372155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 5, 2].length) (baseStart_4372155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4372155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4372155 prefixEnd_4372155 := by exact prefixLift 4372155
  have htrace : WordTrace (prefixWord ++ tailWord_4372155) baseStart_4372155 baseEnd_4372155 := by
    simpa [prefixWord, tailWord_4372155, baseEnd_4372155] using wordTrace_append hprefix tailTrace_4372155
  have hstable : (prefixWord ++ tailWord_4372155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4372155).length < 2 ^ (prefixWord ++ tailWord_4372155).sum := by decide
  have hdescent : baseEnd_4372155 < baseStart_4372155 := by decide
  rcases family_descends (prefixWord ++ tailWord_4372155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4372202 : List Nat := [3, 1, 3, 1, 1, 1, 5, 1, 2, 1, 4]
def baseStart_4372202 : Nat := 118140960795 + 4372202 * 2 ^ 59
def prefixEnd_4372202 : Nat := 4983230072969 + 3 ^ 40 * 4372202 * 2
def baseEnd_4372202 : Nat := 2245041144549207973267615

theorem tailTrace_4372202 : CollatzResearch.WordTrace tailWord_4372202 prefixEnd_4372202 2245041144549207973267615 := by
  unfold tailWord_4372202
  simp only [CollatzResearch.WordTrace]
  refine ⟨39866826926566585374469715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106311538470844227665252573 39866826926566585374469715)
  ·
    refine ⟨59800240389849878061704573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39866826926566585374469715 59800240389849878061704573)
    ·
      refine ⟨22425090146193704273139215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59800240389849878061704573 22425090146193704273139215)
      ·
        refine ⟨33637635219290556409708823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22425090146193704273139215 33637635219290556409708823)
        ·
          refine ⟨50456452828935834614563235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33637635219290556409708823 50456452828935834614563235)
          ·
            refine ⟨75684679243403751921844853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50456452828935834614563235 75684679243403751921844853)
            ·
              refine ⟨7095438679069101742672955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 75684679243403751921844853 7095438679069101742672955)
              ·
                refine ⟨10643158018603652614009433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7095438679069101742672955 10643158018603652614009433)
                ·
                  refine ⟨7982368513952739460507075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10643158018603652614009433 7982368513952739460507075)
                  ·
                    refine ⟨11973552770929109190760613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7982368513952739460507075 11973552770929109190760613)
                    ·
                      refine ⟨2245041144549207973267615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11973552770929109190760613 2245041144549207973267615)
                      ·
                        rfl

theorem cell23_4372202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 1, 2, 1, 4].length) (baseStart_4372202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4372202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4372202 prefixEnd_4372202 := by exact prefixLift 4372202
  have htrace : WordTrace (prefixWord ++ tailWord_4372202) baseStart_4372202 baseEnd_4372202 := by
    simpa [prefixWord, tailWord_4372202, baseEnd_4372202] using wordTrace_append hprefix tailTrace_4372202
  have hstable : (prefixWord ++ tailWord_4372202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4372202).length < 2 ^ (prefixWord ++ tailWord_4372202).sum := by decide
  have hdescent : baseEnd_4372202 < baseStart_4372202 := by decide
  rcases family_descends (prefixWord ++ tailWord_4372202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4372286 : List Nat := [4, 2, 1, 2, 2, 1, 3, 1, 3, 1, 3]
def baseStart_4372286 : Nat := 118140960795 + 4372286 * 2 ^ 59
def prefixEnd_4372286 : Nat := 4983230072969 + 3 ^ 40 * 4372286 * 2
def baseEnd_4372286 : Nat := 2245084276924185644617229

theorem tailTrace_4372286 : CollatzResearch.WordTrace tailWord_4372286 prefixEnd_4372286 2245084276924185644617229 := by
  unfold tailWord_4372286
  simp only [CollatzResearch.WordTrace]
  refine ⟨19933796429745252980492089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106313580958641349229291141 19933796429745252980492089)
  ·
    refine ⟨14950347322308939735369067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19933796429745252980492089 14950347322308939735369067)
    ·
      refine ⟨22425520983463409603053601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14950347322308939735369067 22425520983463409603053601)
      ·
        refine ⟨16819140737597557202290201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22425520983463409603053601 16819140737597557202290201)
        ·
          refine ⟨12614355553198167901717651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16819140737597557202290201 12614355553198167901717651)
          ·
            refine ⟨18921533329797251852576477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12614355553198167901717651 18921533329797251852576477)
            ·
              refine ⟨7095574998673969444716179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18921533329797251852576477 7095574998673969444716179)
              ·
                refine ⟨10643362498010954167074269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7095574998673969444716179 10643362498010954167074269)
                ·
                  refine ⟨3991260936754107812652851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10643362498010954167074269 3991260936754107812652851)
                  ·
                    refine ⟨5986891405131161718979277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3991260936754107812652851 5986891405131161718979277)
                    ·
                      refine ⟨2245084276924185644617229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5986891405131161718979277 2245084276924185644617229)
                      ·
                        rfl

theorem cell23_4372286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_4372286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4372286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4372286 prefixEnd_4372286 := by exact prefixLift 4372286
  have htrace : WordTrace (prefixWord ++ tailWord_4372286) baseStart_4372286 baseEnd_4372286 := by
    simpa [prefixWord, tailWord_4372286, baseEnd_4372286] using wordTrace_append hprefix tailTrace_4372286
  have hstable : (prefixWord ++ tailWord_4372286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4372286).length < 2 ^ (prefixWord ++ tailWord_4372286).sum := by decide
  have hdescent : baseEnd_4372286 < baseStart_4372286 := by decide
  rcases family_descends (prefixWord ++ tailWord_4372286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4372309 : List Nat := [1, 3, 2, 2, 2, 2, 3, 2, 1, 1, 4]
def baseStart_4372309 : Nat := 118140960795 + 4372309 * 2 ^ 59
def prefixEnd_4372309 : Nat := 4983230072969 + 3 ^ 40 * 4372309 * 2
def baseEnd_4372309 : Nat := 2245096086979239054629623

theorem tailTrace_4372309 : CollatzResearch.WordTrace tailWord_4372309 prefixEnd_4372309 2245096086979239054629623 := by
  unfold tailWord_4372309
  simp only [CollatzResearch.WordTrace]
  refine ⟨159471210316878698772023981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106314140211252465848015987 159471210316878698772023981)
  ·
    refine ⟨59801703868829512039508993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159471210316878698772023981 59801703868829512039508993)
    ·
      refine ⟨44851277901622134029631745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59801703868829512039508993 44851277901622134029631745)
      ·
        refine ⟨33638458426216600522223809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44851277901622134029631745 33638458426216600522223809)
        ·
          refine ⟨25228843819662450391667857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33638458426216600522223809 25228843819662450391667857)
          ·
            refine ⟨18921632864746837793750893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25228843819662450391667857 18921632864746837793750893)
            ·
              refine ⟨7095612324280064172656585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18921632864746837793750893 7095612324280064172656585)
              ·
                refine ⟨5321709243210048129492439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7095612324280064172656585 5321709243210048129492439)
                ·
                  refine ⟨7982563864815072194238659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5321709243210048129492439 7982563864815072194238659)
                  ·
                    refine ⟨11973845797222608291357989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7982563864815072194238659 11973845797222608291357989)
                    ·
                      refine ⟨2245096086979239054629623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11973845797222608291357989 2245096086979239054629623)
                      ·
                        rfl

theorem cell23_4372309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 2, 1, 1, 4].length) (baseStart_4372309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4372309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4372309 prefixEnd_4372309 := by exact prefixLift 4372309
  have htrace : WordTrace (prefixWord ++ tailWord_4372309) baseStart_4372309 baseEnd_4372309 := by
    simpa [prefixWord, tailWord_4372309, baseEnd_4372309] using wordTrace_append hprefix tailTrace_4372309
  have hstable : (prefixWord ++ tailWord_4372309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4372309).length < 2 ^ (prefixWord ++ tailWord_4372309).sum := by decide
  have hdescent : baseEnd_4372309 < baseStart_4372309 := by decide
  rcases family_descends (prefixWord ++ tailWord_4372309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4372345 : List Nat := [1, 2, 1, 3, 2, 2, 1, 1, 1, 9]
def baseStart_4372345 : Nat := 118140960795 + 4372345 * 2 ^ 59
def prefixEnd_4372345 : Nat := 4983230072969 + 3 ^ 40 * 4372345 * 2
def baseEnd_4372345 : Nat := 748371524094266971259819

theorem tailTrace_4372345 : CollatzResearch.WordTrace tailWord_4372345 prefixEnd_4372345 748371524094266971259819 := by
  unfold tailWord_4372345
  simp only [CollatzResearch.WordTrace]
  refine ⟨159472523344748276920334489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106315015563165517946889659 159472523344748276920334489)
  ·
    refine ⟨119604392508561207690250867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159472523344748276920334489 119604392508561207690250867)
    ·
      refine ⟨179406588762841811535376301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119604392508561207690250867 179406588762841811535376301)
      ·
        refine ⟨67277470786065679325766113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 179406588762841811535376301 67277470786065679325766113)
        ·
          refine ⟨50458103089549259494324585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67277470786065679325766113 50458103089549259494324585)
          ·
            refine ⟨37843577317161944620743439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50458103089549259494324585 37843577317161944620743439)
            ·
              refine ⟨56765365975742916931115159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37843577317161944620743439 56765365975742916931115159)
              ·
                refine ⟨85148048963614375396672739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56765365975742916931115159 85148048963614375396672739)
                ·
                  refine ⟨127722073445421563095009109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85148048963614375396672739 127722073445421563095009109)
                  ·
                    refine ⟨748371524094266971259819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 127722073445421563095009109 748371524094266971259819)
                    ·
                      rfl

theorem cell23_4372345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 9].length) (baseStart_4372345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4372345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4372345 prefixEnd_4372345 := by exact prefixLift 4372345
  have htrace : WordTrace (prefixWord ++ tailWord_4372345) baseStart_4372345 baseEnd_4372345 := by
    simpa [prefixWord, tailWord_4372345, baseEnd_4372345] using wordTrace_append hprefix tailTrace_4372345
  have hstable : (prefixWord ++ tailWord_4372345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4372345).length < 2 ^ (prefixWord ++ tailWord_4372345).sum := by decide
  have hdescent : baseEnd_4372345 < baseStart_4372345 := by decide
  rcases family_descends (prefixWord ++ tailWord_4372345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4372366 : List Nat := [4, 1, 1, 5, 1, 1, 3, 7]
def baseStart_4372366 : Nat := 118140960795 + 4372366 * 2 ^ 59
def prefixEnd_4372366 : Nat := 4983230072969 + 3 ^ 40 * 4372366 * 2
def baseEnd_4372366 : Nat := 83152790939872049319143

theorem tailTrace_4372366 : CollatzResearch.WordTrace tailWord_4372366 prefixEnd_4372366 83152790939872049319143 := by
  unfold tailWord_4372366
  simp only [CollatzResearch.WordTrace]
  refine ⟨19934161159709024688356119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106315526185114798337899301 19934161159709024688356119)
  ·
    refine ⟨29901241739563537032534179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19934161159709024688356119 29901241739563537032534179)
    ·
      refine ⟨44851862609345305548801269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29901241739563537032534179 44851862609345305548801269)
      ·
        refine ⟨4204862119626122395200119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44851862609345305548801269 4204862119626122395200119)
        ·
          refine ⟨6307293179439183592800179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4204862119626122395200119 6307293179439183592800179)
          ·
            refine ⟨9460939769158775389200269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6307293179439183592800179 9460939769158775389200269)
            ·
              refine ⟨3547852413434540770950101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9460939769158775389200269 3547852413434540770950101)
              ·
                refine ⟨83152790939872049319143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3547852413434540770950101 83152790939872049319143)
                ·
                  rfl

theorem cell23_4372366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 3, 7].length) (baseStart_4372366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4372366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4372366 prefixEnd_4372366 := by exact prefixLift 4372366
  have htrace : WordTrace (prefixWord ++ tailWord_4372366) baseStart_4372366 baseEnd_4372366 := by
    simpa [prefixWord, tailWord_4372366, baseEnd_4372366] using wordTrace_append hprefix tailTrace_4372366
  have hstable : (prefixWord ++ tailWord_4372366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4372366).length < 2 ^ (prefixWord ++ tailWord_4372366).sum := by decide
  have hdescent : baseEnd_4372366 < baseStart_4372366 := by decide
  rcases family_descends (prefixWord ++ tailWord_4372366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4372369 : List Nat := [1, 2, 2, 1, 1, 1, 6, 1, 3, 3, 2]
def baseStart_4372369 : Nat := 118140960795 + 4372369 * 2 ^ 59
def prefixEnd_4372369 : Nat := 4983230072969 + 3 ^ 40 * 4372369 * 2
def baseEnd_4372369 : Nat := 2245126895818508819879347

theorem tailTrace_4372369 : CollatzResearch.WordTrace tailWord_4372369 prefixEnd_4372369 2245126895818508819879347 := by
  unfold tailWord_4372369
  simp only [CollatzResearch.WordTrace]
  refine ⟨159473398696661329019208161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106315599131107552679472107 159473398696661329019208161)
  ·
    refine ⟨119605049022495996764406121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159473398696661329019208161 119605049022495996764406121)
    ·
      refine ⟨89703786766871997573304591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119605049022495996764406121 89703786766871997573304591)
      ·
        refine ⟨134555680150307996359956887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89703786766871997573304591 134555680150307996359956887)
        ·
          refine ⟨201833520225461994539935331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134555680150307996359956887 201833520225461994539935331)
          ·
            refine ⟨302750280338192991809902997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201833520225461994539935331 302750280338192991809902997)
            ·
              refine ⟨14191419390852796491089203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 302750280338192991809902997 14191419390852796491089203)
              ·
                refine ⟨21287129086279194736633805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14191419390852796491089203 21287129086279194736633805)
                ·
                  refine ⟨7982673407354698026237677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21287129086279194736633805 7982673407354698026237677)
                  ·
                    refine ⟨2993502527758011759839129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7982673407354698026237677 2993502527758011759839129)
                    ·
                      refine ⟨2245126895818508819879347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2993502527758011759839129 2245126895818508819879347)
                      ·
                        rfl

theorem cell23_4372369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 3, 2].length) (baseStart_4372369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4372369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4372369 prefixEnd_4372369 := by exact prefixLift 4372369
  have htrace : WordTrace (prefixWord ++ tailWord_4372369) baseStart_4372369 baseEnd_4372369 := by
    simpa [prefixWord, tailWord_4372369, baseEnd_4372369] using wordTrace_append hprefix tailTrace_4372369
  have hstable : (prefixWord ++ tailWord_4372369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4372369).length < 2 ^ (prefixWord ++ tailWord_4372369).sum := by decide
  have hdescent : baseEnd_4372369 < baseStart_4372369 := by decide
  rcases family_descends (prefixWord ++ tailWord_4372369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4372395 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 6]
def baseStart_4372395 : Nat := 118140960795 + 4372395 * 2 ^ 59
def prefixEnd_4372395 : Nat := 4983230072969 + 3 ^ 40 * 4372395 * 2
def baseEnd_4372395 : Nat := 2245140246315525718154227

theorem tailTrace_4372395 : CollatzResearch.WordTrace tailWord_4372395 prefixEnd_4372395 2245140246315525718154227 := by
  unfold tailWord_4372395
  simp only [CollatzResearch.WordTrace]
  refine ⟨159474346994567135459654639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106316231329711423639769759 159474346994567135459654639)
  ·
    refine ⟨239211520491850703189481959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159474346994567135459654639 239211520491850703189481959)
    ·
      refine ⟨358817280737776054784222939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239211520491850703189481959 358817280737776054784222939)
      ·
        refine ⟨538225921106664082176334409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 358817280737776054784222939 538225921106664082176334409)
        ·
          refine ⟨403669440829998061632250807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 538225921106664082176334409 403669440829998061632250807)
          ·
            refine ⟨605504161244997092448376211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 403669440829998061632250807 605504161244997092448376211)
            ·
              refine ⟨908256241867495638672564317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 605504161244997092448376211 908256241867495638672564317)
              ·
                refine ⟨340596090700310864502211619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 908256241867495638672564317 340596090700310864502211619)
                ·
                  refine ⟨510894136050466296753317429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 340596090700310864502211619 510894136050466296753317429)
                  ·
                    refine ⟨47896325254731215320623509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 510894136050466296753317429 47896325254731215320623509)
                    ·
                      refine ⟨2245140246315525718154227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47896325254731215320623509 2245140246315525718154227)
                      ·
                        rfl

theorem cell23_4372395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 6].length) (baseStart_4372395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4372395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4372395 prefixEnd_4372395 := by exact prefixLift 4372395
  have htrace : WordTrace (prefixWord ++ tailWord_4372395) baseStart_4372395 baseEnd_4372395 := by
    simpa [prefixWord, tailWord_4372395, baseEnd_4372395] using wordTrace_append hprefix tailTrace_4372395
  have hstable : (prefixWord ++ tailWord_4372395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4372395).length < 2 ^ (prefixWord ++ tailWord_4372395).sum := by decide
  have hdescent : baseEnd_4372395 < baseStart_4372395 := by decide
  rcases family_descends (prefixWord ++ tailWord_4372395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4372402 : List Nat := [3, 2, 1, 1, 1, 1, 1, 3, 1, 6, 3]
def baseStart_4372402 : Nat := 118140960795 + 4372402 * 2 ^ 59
def prefixEnd_4372402 : Nat := 4983230072969 + 3 ^ 40 * 4372402 * 2
def baseEnd_4372402 : Nat := 2245143840680107190766695

theorem tailTrace_4372402 : CollatzResearch.WordTrace tailWord_4372402 prefixEnd_4372402 2245143840680107190766695 := by
  unfold tailWord_4372402
  simp only [CollatzResearch.WordTrace]
  refine ⟨39868650576385443913789865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106316401537027850436772973 39868650576385443913789865)
  ·
    refine ⟨29901487932289082935342399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39868650576385443913789865 29901487932289082935342399)
    ·
      refine ⟨44852231898433624403013599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29901487932289082935342399 44852231898433624403013599)
      ·
        refine ⟨67278347847650436604520399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44852231898433624403013599 67278347847650436604520399)
        ·
          refine ⟨100917521771475654906780599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67278347847650436604520399 100917521771475654906780599)
          ·
            refine ⟨151376282657213482360170899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100917521771475654906780599 151376282657213482360170899)
            ·
              refine ⟨227064423985820223540256349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151376282657213482360170899 227064423985820223540256349)
              ·
                refine ⟨85149158994682583827596131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 227064423985820223540256349 85149158994682583827596131)
                ·
                  refine ⟨127723738492023875741394197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85149158994682583827596131 127723738492023875741394197)
                  ·
                    refine ⟨5987050241813619175377853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 127723738492023875741394197 5987050241813619175377853)
                    ·
                      refine ⟨2245143840680107190766695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5987050241813619175377853 2245143840680107190766695)
                      ·
                        rfl

theorem cell23_4372402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 1, 6, 3].length) (baseStart_4372402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4372402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4372402 prefixEnd_4372402 := by exact prefixLift 4372402
  have htrace : WordTrace (prefixWord ++ tailWord_4372402) baseStart_4372402 baseEnd_4372402 := by
    simpa [prefixWord, tailWord_4372402, baseEnd_4372402] using wordTrace_append hprefix tailTrace_4372402
  have hstable : (prefixWord ++ tailWord_4372402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4372402).length < 2 ^ (prefixWord ++ tailWord_4372402).sum := by decide
  have hdescent : baseEnd_4372402 < baseStart_4372402 := by decide
  rcases family_descends (prefixWord ++ tailWord_4372402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4372432 : List Nat := [2, 1, 1, 1, 1, 2, 4, 2, 1, 5, 3]
def baseStart_4372432 : Nat := 118140960795 + 4372432 * 2 ^ 59
def prefixEnd_4372432 : Nat := 4983230072969 + 3 ^ 40 * 4372432 * 2
def baseEnd_4372432 : Nat := 2245159245099742073391557

theorem tailTrace_4372432 : CollatzResearch.WordTrace tailWord_4372432 prefixEnd_4372432 2245159245099742073391557 := by
  unfold tailWord_4372432
  simp only [CollatzResearch.WordTrace]
  refine ⟨79737848247716545389375775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106317130996955393852501033 79737848247716545389375775)
  ·
    refine ⟨119606772371574818084063663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79737848247716545389375775 119606772371574818084063663)
    ·
      refine ⟨179410158557362227126095495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119606772371574818084063663 179410158557362227126095495)
      ·
        refine ⟨269115237836043340689143243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179410158557362227126095495 269115237836043340689143243)
        ·
          refine ⟨403672856754065011033714865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 269115237836043340689143243 403672856754065011033714865)
          ·
            refine ⟨302754642565548758275286149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 403672856754065011033714865 302754642565548758275286149)
            ·
              refine ⟨56766495481040392176616153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 302754642565548758275286149 56766495481040392176616153)
              ·
                refine ⟨42574871610780294132462115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56766495481040392176616153 42574871610780294132462115)
                ·
                  refine ⟨63862307416170441198693173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42574871610780294132462115 63862307416170441198693173)
                  ·
                    refine ⟨5987091320265978862377485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 63862307416170441198693173 5987091320265978862377485)
                    ·
                      refine ⟨2245159245099742073391557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5987091320265978862377485 2245159245099742073391557)
                      ·
                        rfl

theorem cell23_4372432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 1, 5, 3].length) (baseStart_4372432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4372432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4372432 prefixEnd_4372432 := by exact prefixLift 4372432
  have htrace : WordTrace (prefixWord ++ tailWord_4372432) baseStart_4372432 baseEnd_4372432 := by
    simpa [prefixWord, tailWord_4372432, baseEnd_4372432] using wordTrace_append hprefix tailTrace_4372432
  have hstable : (prefixWord ++ tailWord_4372432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4372432).length < 2 ^ (prefixWord ++ tailWord_4372432).sum := by decide
  have hdescent : baseEnd_4372432 < baseStart_4372432 := by decide
  rcases family_descends (prefixWord ++ tailWord_4372432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4372472 : List Nat := [2, 1, 2, 1, 1, 3, 2, 1, 3, 3, 4]
def baseStart_4372472 : Nat := 118140960795 + 4372472 * 2 ^ 59
def prefixEnd_4372472 : Nat := 4983230072969 + 3 ^ 40 * 4372472 * 2
def baseEnd_4372472 : Nat := 2245179784325921916891373

theorem tailTrace_4372472 : CollatzResearch.WordTrace tailWord_4372472 prefixEnd_4372472 2245179784325921916891373 := by
  unfold tailWord_4372472
  simp only [CollatzResearch.WordTrace]
  refine ⟨79738577707644088805103835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106318103610192118406805113 79738577707644088805103835)
  ·
    refine ⟨119607866561466133207655753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79738577707644088805103835 119607866561466133207655753)
    ·
      refine ⟨89705899921099599905741815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119607866561466133207655753 89705899921099599905741815)
      ·
        refine ⟨134558849881649399858612723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89705899921099599905741815 134558849881649399858612723)
        ·
          refine ⟨201838274822474099787919085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134558849881649399858612723 201838274822474099787919085)
          ·
            refine ⟨75689353058427787420469657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 201838274822474099787919085 75689353058427787420469657)
            ·
              refine ⟨56767014793820840565352243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75689353058427787420469657 56767014793820840565352243)
              ·
                refine ⟨85150522190731260848028365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56767014793820840565352243 85150522190731260848028365)
                ·
                  refine ⟨31931445821524222818010637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 85150522190731260848028365 31931445821524222818010637)
                  ·
                    refine ⟨11974292183071583556753989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31931445821524222818010637 11974292183071583556753989)
                    ·
                      refine ⟨2245179784325921916891373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11974292183071583556753989 2245179784325921916891373)
                      ·
                        rfl

theorem cell23_4372472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 3, 3, 4].length) (baseStart_4372472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4372472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4372472 prefixEnd_4372472 := by exact prefixLift 4372472
  have htrace : WordTrace (prefixWord ++ tailWord_4372472) baseStart_4372472 baseEnd_4372472 := by
    simpa [prefixWord, tailWord_4372472, baseEnd_4372472] using wordTrace_append hprefix tailTrace_4372472
  have hstable : (prefixWord ++ tailWord_4372472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4372472).length < 2 ^ (prefixWord ++ tailWord_4372472).sum := by decide
  have hdescent : baseEnd_4372472 < baseStart_4372472 := by decide
  rcases family_descends (prefixWord ++ tailWord_4372472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4372489 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 6, 4, 2]
def baseStart_4372489 : Nat := 118140960795 + 4372489 * 2 ^ 59
def prefixEnd_4372489 : Nat := 4983230072969 + 3 ^ 40 * 4372489 * 2
def baseEnd_4372489 : Nat := 2245188513497048350378795

theorem tailTrace_4372489 : CollatzResearch.WordTrace tailWord_4372489 prefixEnd_4372489 2245188513497048350378795 := by
  unfold tailWord_4372489
  simp only [CollatzResearch.WordTrace]
  refine ⟨159477775456226589513576521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106318516970817726342384347 159477775456226589513576521)
  ·
    refine ⟨119608331592169942135182391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159477775456226589513576521 119608331592169942135182391)
    ·
      refine ⟨179412497388254913202773587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119608331592169942135182391 179412497388254913202773587)
      ·
        refine ⟨269118746082382369804160381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179412497388254913202773587 269118746082382369804160381)
        ·
          refine ⟨100919529780893388676560143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 269118746082382369804160381 100919529780893388676560143)
          ·
            refine ⟨151379294671340083014840215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100919529780893388676560143 151379294671340083014840215)
            ·
              refine ⟨227068942007010124522260323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151379294671340083014840215 227068942007010124522260323)
              ·
                refine ⟨340603413010515186783390485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 227068942007010124522260323 340603413010515186783390485)
                ·
                  refine ⟨15965784984867899380471429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 340603413010515186783390485 15965784984867899380471429)
                  ·
                    refine ⟨2993584684662731133838393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15965784984867899380471429 2993584684662731133838393)
                    ·
                      refine ⟨2245188513497048350378795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2993584684662731133838393 2245188513497048350378795)
                      ·
                        rfl

theorem cell23_4372489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 6, 4, 2].length) (baseStart_4372489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4372489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4372489 prefixEnd_4372489 := by exact prefixLift 4372489
  have htrace : WordTrace (prefixWord ++ tailWord_4372489) baseStart_4372489 baseEnd_4372489 := by
    simpa [prefixWord, tailWord_4372489, baseEnd_4372489] using wordTrace_append hprefix tailTrace_4372489
  have hstable : (prefixWord ++ tailWord_4372489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4372489).length < 2 ^ (prefixWord ++ tailWord_4372489).sum := by decide
  have hdescent : baseEnd_4372489 < baseStart_4372489 := by decide
  rcases family_descends (prefixWord ++ tailWord_4372489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4372529 : List Nat := [1, 2, 2, 3, 1, 3, 2, 3, 6]
def baseStart_4372529 : Nat := 118140960795 + 4372529 * 2 ^ 59
def prefixEnd_4372529 : Nat := 4983230072969 + 3 ^ 40 * 4372529 * 2
def baseEnd_4372529 : Nat := 249467672524803132653179

theorem tailTrace_4372529 : CollatzResearch.WordTrace tailWord_4372529 prefixEnd_4372529 249467672524803132653179 := by
  unfold tailWord_4372529
  simp only [CollatzResearch.WordTrace]
  refine ⟨159479234376081676345032641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106319489584054450896688427 159479234376081676345032641)
  ·
    refine ⟨119609425782061257258774481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159479234376081676345032641 119609425782061257258774481)
    ·
      refine ⟨89707069336545942944080861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119609425782061257258774481 89707069336545942944080861)
      ·
        refine ⟨33640151001204728604030323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89707069336545942944080861 33640151001204728604030323)
        ·
          refine ⟨50460226501807092906045485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33640151001204728604030323 50460226501807092906045485)
          ·
            refine ⟨18922584938177659839767057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50460226501807092906045485 18922584938177659839767057)
            ·
              refine ⟨14191938703633244879825293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18922584938177659839767057 14191938703633244879825293)
              ·
                refine ⟨5321977013862466829934485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14191938703633244879825293 5321977013862466829934485)
                ·
                  refine ⟨249467672524803132653179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5321977013862466829934485 249467672524803132653179)
                  ·
                    rfl

theorem cell23_4372529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 3, 6].length) (baseStart_4372529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4372529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4372529 prefixEnd_4372529 := by exact prefixLift 4372529
  have htrace : WordTrace (prefixWord ++ tailWord_4372529) baseStart_4372529 baseEnd_4372529 := by
    simpa [prefixWord, tailWord_4372529, baseEnd_4372529] using wordTrace_append hprefix tailTrace_4372529
  have hstable : (prefixWord ++ tailWord_4372529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4372529).length < 2 ^ (prefixWord ++ tailWord_4372529).sum := by decide
  have hdescent : baseEnd_4372529 < baseStart_4372529 := by decide
  rcases family_descends (prefixWord ++ tailWord_4372529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4372559 : List Nat := [1, 1, 2, 1, 1, 2, 2, 7, 1, 5]
def baseStart_4372559 : Nat := 118140960795 + 4372559 * 2 ^ 59
def prefixEnd_4372559 : Nat := 4983230072969 + 3 ^ 40 * 4372559 * 2
def baseEnd_4372559 : Nat := 748408152380954358834491

theorem tailTrace_4372559 : CollatzResearch.WordTrace tailWord_4372559 prefixEnd_4372559 748408152380954358834491 := by
  unfold tailWord_4372559
  simp only [CollatzResearch.WordTrace]
  refine ⟨159480328565972991468624731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106320219043981994312416487 159480328565972991468624731)
  ·
    refine ⟨239220492848959487202937097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159480328565972991468624731 239220492848959487202937097)
    ·
      refine ⟨179415369636719615402202823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 239220492848959487202937097 179415369636719615402202823)
      ·
        refine ⟨269123054455079423103304235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179415369636719615402202823 269123054455079423103304235)
        ·
          refine ⟨403684581682619134654956353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 269123054455079423103304235 403684581682619134654956353)
          ·
            refine ⟨302763436261964350991217265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 403684581682619134654956353 302763436261964350991217265)
            ·
              refine ⟨227072577196473263243412949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 302763436261964350991217265 227072577196473263243412949)
              ·
                refine ⟨5322013528042342107267491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 227072577196473263243412949 5322013528042342107267491)
                ·
                  refine ⟨7983020292063513160901237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5322013528042342107267491 7983020292063513160901237)
                  ·
                    refine ⟨748408152380954358834491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7983020292063513160901237 748408152380954358834491)
                    ·
                      rfl

theorem cell23_4372559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 7, 1, 5].length) (baseStart_4372559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4372559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4372559 prefixEnd_4372559 := by exact prefixLift 4372559
  have htrace : WordTrace (prefixWord ++ tailWord_4372559) baseStart_4372559 baseEnd_4372559 := by
    simpa [prefixWord, tailWord_4372559, baseEnd_4372559] using wordTrace_append hprefix tailTrace_4372559
  have hstable : (prefixWord ++ tailWord_4372559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4372559).length < 2 ^ (prefixWord ++ tailWord_4372559).sum := by decide
  have hdescent : baseEnd_4372559 < baseStart_4372559 := by decide
  rcases family_descends (prefixWord ++ tailWord_4372559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4372579 : List Nat := [1, 1, 1, 5, 1, 1, 2, 1, 5, 1, 4]
def baseStart_4372579 : Nat := 118140960795 + 4372579 * 2 ^ 59
def prefixEnd_4372579 : Nat := 4983230072969 + 3 ^ 40 * 4372579 * 2
def baseEnd_4372579 : Nat := 2245234726755952998253381

theorem tailTrace_4372579 : CollatzResearch.WordTrace tailWord_4372579 prefixEnd_4372579 2245234726755952998253381 := by
  unfold tailWord_4372579
  simp only [CollatzResearch.WordTrace]
  refine ⟨159481058025900534884352791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106320705350600356589568527 159481058025900534884352791)
  ·
    refine ⟨239221587038850802326529187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159481058025900534884352791 239221587038850802326529187)
    ·
      refine ⟨358832380558276203489793781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239221587038850802326529187 358832380558276203489793781)
      ·
        refine ⟨33640535677338394077168167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 358832380558276203489793781 33640535677338394077168167)
        ·
          refine ⟨50460803516007591115752251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33640535677338394077168167 50460803516007591115752251)
          ·
            refine ⟨75691205274011386673628377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50460803516007591115752251 75691205274011386673628377)
            ·
              refine ⟨56768403955508540005221283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75691205274011386673628377 56768403955508540005221283)
              ·
                refine ⟨85152605933262810007831925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56768403955508540005221283 85152605933262810007831925)
                ·
                  refine ⟨7983056806243388438234243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 85152605933262810007831925 7983056806243388438234243)
                  ·
                    refine ⟨11974585209365082657351365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7983056806243388438234243 11974585209365082657351365)
                    ·
                      refine ⟨2245234726755952998253381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11974585209365082657351365 2245234726755952998253381)
                      ·
                        rfl

theorem cell23_4372579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_4372579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4372579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4372579 prefixEnd_4372579 := by exact prefixLift 4372579
  have htrace : WordTrace (prefixWord ++ tailWord_4372579) baseStart_4372579 baseEnd_4372579 := by
    simpa [prefixWord, tailWord_4372579, baseEnd_4372579] using wordTrace_append hprefix tailTrace_4372579
  have hstable : (prefixWord ++ tailWord_4372579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4372579).length < 2 ^ (prefixWord ++ tailWord_4372579).sum := by decide
  have hdescent : baseEnd_4372579 < baseStart_4372579 := by decide
  rcases family_descends (prefixWord ++ tailWord_4372579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4372616 : List Nat := [2, 1, 3, 4, 1, 1, 1, 3, 1, 1, 5]
def baseStart_4372616 : Nat := 118140960795 + 4372616 * 2 ^ 59
def prefixEnd_4372616 : Nat := 4983230072969 + 3 ^ 40 * 4372616 * 2
def baseEnd_4372616 : Nat := 2245253725540169353490711

theorem tailTrace_4372616 : CollatzResearch.WordTrace tailWord_4372616 prefixEnd_4372616 2245253725540169353490711 := by
  unfold tailWord_4372616
  simp only [CollatzResearch.WordTrace]
  refine ⟨79741203763383245101724851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106321605017844326802299801 79741203763383245101724851)
  ·
    refine ⟨119611805645074867652587277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79741203763383245101724851 119611805645074867652587277)
    ·
      refine ⟨44854427116903075369720229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119611805645074867652587277 44854427116903075369720229)
      ·
        refine ⟨8410205084419326631822543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44854427116903075369720229 8410205084419326631822543)
        ·
          refine ⟨12615307626628989947733815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8410205084419326631822543 12615307626628989947733815)
          ·
            refine ⟨18922961439943484921600723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12615307626628989947733815 18922961439943484921600723)
            ·
              refine ⟨28384442159915227382401085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18922961439943484921600723 28384442159915227382401085)
              ·
                refine ⟨10644165809968210268400407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28384442159915227382401085 10644165809968210268400407)
                ·
                  refine ⟨15966248714952315402600611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10644165809968210268400407 15966248714952315402600611)
                  ·
                    refine ⟨23949373072428473103900917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15966248714952315402600611 23949373072428473103900917)
                    ·
                      refine ⟨2245253725540169353490711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23949373072428473103900917 2245253725540169353490711)
                      ·
                        rfl

theorem cell23_4372616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_4372616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4372616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4372616 prefixEnd_4372616 := by exact prefixLift 4372616
  have htrace : WordTrace (prefixWord ++ tailWord_4372616) baseStart_4372616 baseEnd_4372616 := by
    simpa [prefixWord, tailWord_4372616, baseEnd_4372616] using wordTrace_append hprefix tailTrace_4372616
  have hstable : (prefixWord ++ tailWord_4372616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4372616).length < 2 ^ (prefixWord ++ tailWord_4372616).sum := by decide
  have hdescent : baseEnd_4372616 < baseStart_4372616 := by decide
  rcases family_descends (prefixWord ++ tailWord_4372616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4372640 : List Nat := [2, 1, 1, 4, 2, 4, 2, 1, 2, 4]
def baseStart_4372640 : Nat := 118140960795 + 4372640 * 2 ^ 59
def prefixEnd_4372640 : Nat := 4983230072969 + 3 ^ 40 * 4372640 * 2
def baseEnd_4372640 : Nat := 748422016358625753196867

theorem tailTrace_4372640 : CollatzResearch.WordTrace tailWord_4372640 prefixEnd_4372640 748422016358625753196867 := by
  unfold tailWord_4372640
  simp only [CollatzResearch.WordTrace]
  refine ⟨79741641439339771151161687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106322188585786361534882249 79741641439339771151161687)
  ·
    refine ⟨119612462159009656726742531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79741641439339771151161687 119612462159009656726742531)
    ·
      refine ⟨179418693238514485090113797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119612462159009656726742531 179418693238514485090113797)
      ·
        refine ⟨33641004982221465954396337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 179418693238514485090113797 33641004982221465954396337)
        ·
          refine ⟨25230753736666099465797253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33641004982221465954396337 25230753736666099465797253)
          ·
            refine ⟨4730766325624893649836985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25230753736666099465797253 4730766325624893649836985)
            ·
              refine ⟨3548074744218670237377739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4730766325624893649836985 3548074744218670237377739)
              ·
                refine ⟨5322112116328005356066609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3548074744218670237377739 5322112116328005356066609)
                ·
                  refine ⟨3991584087246004017049957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5322112116328005356066609 3991584087246004017049957)
                  ·
                    refine ⟨748422016358625753196867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3991584087246004017049957 748422016358625753196867)
                    ·
                      rfl

theorem cell23_4372640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 2, 1, 2, 4].length) (baseStart_4372640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4372640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4372640 prefixEnd_4372640 := by exact prefixLift 4372640
  have htrace : WordTrace (prefixWord ++ tailWord_4372640) baseStart_4372640 baseEnd_4372640 := by
    simpa [prefixWord, tailWord_4372640, baseEnd_4372640] using wordTrace_append hprefix tailTrace_4372640
  have hstable : (prefixWord ++ tailWord_4372640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4372640).length < 2 ^ (prefixWord ++ tailWord_4372640).sum := by decide
  have hdescent : baseEnd_4372640 < baseStart_4372640 := by decide
  rcases family_descends (prefixWord ++ tailWord_4372640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4372647 : List Nat := [1, 1, 6, 2, 3, 1, 1, 2, 1, 1, 4]
def baseStart_4372647 : Nat := 118140960795 + 4372647 * 2 ^ 59
def prefixEnd_4372647 : Nat := 4983230072969 + 3 ^ 40 * 4372647 * 2
def baseEnd_4372647 : Nat := 2245269643440458732203069

theorem tailTrace_4372647 : CollatzResearch.WordTrace tailWord_4372647 prefixEnd_4372647 2245269643440458732203069 := by
  unfold tailWord_4372647
  simp only [CollatzResearch.WordTrace]
  refine ⟨159483538189654182497828195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106322358793102788331885463 159483538189654182497828195)
  ·
    refine ⟨239225307284481273746742293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159483538189654182497828195 239225307284481273746742293)
    ·
      refine ⟨11213686278960059706878545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 239225307284481273746742293 11213686278960059706878545)
      ·
        refine ⟨8410264709220044780158909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11213686278960059706878545 8410264709220044780158909)
        ·
          refine ⟨3153849265957516792559591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8410264709220044780158909 3153849265957516792559591)
          ·
            refine ⟨4730773898936275188839387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3153849265957516792559591 4730773898936275188839387)
            ·
              refine ⟨7096160848404412783259081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4730773898936275188839387 7096160848404412783259081)
              ·
                refine ⟨5322120636303309587444311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7096160848404412783259081 5322120636303309587444311)
                ·
                  refine ⟨7983180954454964381166467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5322120636303309587444311 7983180954454964381166467)
                  ·
                    refine ⟨11974771431682446571749701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7983180954454964381166467 11974771431682446571749701)
                    ·
                      refine ⟨2245269643440458732203069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11974771431682446571749701 2245269643440458732203069)
                      ·
                        rfl

theorem cell23_4372647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_4372647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4372647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4372647 prefixEnd_4372647 := by exact prefixLift 4372647
  have htrace : WordTrace (prefixWord ++ tailWord_4372647) baseStart_4372647 baseEnd_4372647 := by
    simpa [prefixWord, tailWord_4372647, baseEnd_4372647] using wordTrace_append hprefix tailTrace_4372647
  have hstable : (prefixWord ++ tailWord_4372647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4372647).length < 2 ^ (prefixWord ++ tailWord_4372647).sum := by decide
  have hdescent : baseEnd_4372647 < baseStart_4372647 := by decide
  rcases family_descends (prefixWord ++ tailWord_4372647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4372650 : List Nat := [3, 1, 5, 1, 2, 1, 1, 1, 3, 2, 3]
def baseStart_4372650 : Nat := 118140960795 + 4372650 * 2 ^ 59
def prefixEnd_4372650 : Nat := 4983230072969 + 3 ^ 40 * 4372650 * 2
def baseEnd_4372650 : Nat := 2245271183882422220465555

theorem tailTrace_4372650 : CollatzResearch.WordTrace tailWord_4372650 prefixEnd_4372650 2245271183882422220465555 := by
  unfold tailWord_4372650
  simp only [CollatzResearch.WordTrace]
  refine ⟨39870911902160828502546851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106322431739095542673458269 39870911902160828502546851)
  ·
    refine ⟨59806367853241242753820277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39870911902160828502546851 59806367853241242753820277)
    ·
      refine ⟨5606846986241366508170651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59806367853241242753820277 5606846986241366508170651)
      ·
        refine ⟨8410270479362049762255977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5606846986241366508170651 8410270479362049762255977)
        ·
          refine ⟨6307702859521537321691983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8410270479362049762255977 6307702859521537321691983)
          ·
            refine ⟨9461554289282305982537975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6307702859521537321691983 9461554289282305982537975)
            ·
              refine ⟨14192331433923458973806963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9461554289282305982537975 14192331433923458973806963)
              ·
                refine ⟨21288497150885188460710445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14192331433923458973806963 21288497150885188460710445)
                ·
                  refine ⟨7983186431581945672766417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21288497150885188460710445 7983186431581945672766417)
                  ·
                    refine ⟨5987389823686459254574813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7983186431581945672766417 5987389823686459254574813)
                    ·
                      refine ⟨2245271183882422220465555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5987389823686459254574813 2245271183882422220465555)
                      ·
                        rfl

theorem cell23_4372650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_4372650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4372650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4372650 prefixEnd_4372650 := by exact prefixLift 4372650
  have htrace : WordTrace (prefixWord ++ tailWord_4372650) baseStart_4372650 baseEnd_4372650 := by
    simpa [prefixWord, tailWord_4372650, baseEnd_4372650] using wordTrace_append hprefix tailTrace_4372650
  have hstable : (prefixWord ++ tailWord_4372650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4372650).length < 2 ^ (prefixWord ++ tailWord_4372650).sum := by decide
  have hdescent : baseEnd_4372650 < baseStart_4372650 := by decide
  rcases family_descends (prefixWord ++ tailWord_4372650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4372686 : List Nat := [4, 1, 1, 1, 4, 1, 1, 1, 2, 3, 4]
def baseStart_4372686 : Nat := 118140960795 + 4372686 * 2 ^ 59
def prefixEnd_4372686 : Nat := 4983230072969 + 3 ^ 40 * 4372686 * 2
def baseEnd_4372686 : Nat := 2245289669185984079615389

theorem tailTrace_4372686 : CollatzResearch.WordTrace tailWord_4372686 prefixEnd_4372686 2245289669185984079615389 := by
  unfold tailWord_4372686
  simp only [CollatzResearch.WordTrace]
  refine ⟨19935620079564111519812239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106323307091008594772331941 19935620079564111519812239)
  ·
    refine ⟨29903430119346167279718359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19935620079564111519812239 29903430119346167279718359)
    ·
      refine ⟨44855145179019250919577539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29903430119346167279718359 44855145179019250919577539)
      ·
        refine ⟨67282717768528876379366309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44855145179019250919577539 67282717768528876379366309)
        ·
          refine ⟨12615509581599164321131183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67282717768528876379366309 12615509581599164321131183)
          ·
            refine ⟨18923264372398746481696775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12615509581599164321131183 18923264372398746481696775)
            ·
              refine ⟨28384896558598119722545163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18923264372398746481696775 28384896558598119722545163)
              ·
                refine ⟨42577344837897179583817745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28384896558598119722545163 42577344837897179583817745)
                ·
                  refine ⟨31933008628422884687863309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42577344837897179583817745 31933008628422884687863309)
                  ·
                    refine ⟨11974878235658581757948741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31933008628422884687863309 11974878235658581757948741)
                    ·
                      refine ⟨2245289669185984079615389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11974878235658581757948741 2245289669185984079615389)
                      ·
                        rfl

theorem cell23_4372686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 2, 3, 4].length) (baseStart_4372686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4372686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4372686 prefixEnd_4372686 := by exact prefixLift 4372686
  have htrace : WordTrace (prefixWord ++ tailWord_4372686) baseStart_4372686 baseEnd_4372686 := by
    simpa [prefixWord, tailWord_4372686, baseEnd_4372686] using wordTrace_append hprefix tailTrace_4372686
  have hstable : (prefixWord ++ tailWord_4372686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4372686).length < 2 ^ (prefixWord ++ tailWord_4372686).sum := by decide
  have hdescent : baseEnd_4372686 < baseStart_4372686 := by decide
  rcases family_descends (prefixWord ++ tailWord_4372686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4372689 : List Nat := [1, 2, 2, 1, 2, 2, 2, 2, 1, 3, 5]
def baseStart_4372689 : Nat := 118140960795 + 4372689 * 2 ^ 59
def prefixEnd_4372689 : Nat := 4983230072969 + 3 ^ 40 * 4372689 * 2
def baseEnd_4372689 : Nat := 2245291209627947567877875

theorem tailTrace_4372689 : CollatzResearch.WordTrace tailWord_4372689 prefixEnd_4372689 2245291209627947567877875 := by
  unfold tailWord_4372689
  simp only [CollatzResearch.WordTrace]
  refine ⟨159485070055502023670857121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106323380037001349113904747 159485070055502023670857121)
  ·
    refine ⟨119613802541626517753142841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159485070055502023670857121 119613802541626517753142841)
    ·
      refine ⟨89710351906219888314857131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119613802541626517753142841 89710351906219888314857131)
      ·
        refine ⟨134565527859329832472285697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89710351906219888314857131 134565527859329832472285697)
        ·
          refine ⟨100924145894497374354214273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134565527859329832472285697 100924145894497374354214273)
          ·
            refine ⟨75693109420873030765660705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100924145894497374354214273 75693109420873030765660705)
            ·
              refine ⟨56769832065654773074245529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75693109420873030765660705 56769832065654773074245529)
              ·
                refine ⟨42577374049241079805684147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56769832065654773074245529 42577374049241079805684147)
                ·
                  refine ⟨63866061073861619708526221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42577374049241079805684147 63866061073861619708526221)
                  ·
                    refine ⟨23949772902698107390697333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 63866061073861619708526221 23949772902698107390697333)
                    ·
                      refine ⟨2245291209627947567877875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23949772902698107390697333 2245291209627947567877875)
                      ·
                        rfl

theorem cell23_4372689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 3, 5].length) (baseStart_4372689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4372689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4372689 prefixEnd_4372689 := by exact prefixLift 4372689
  have htrace : WordTrace (prefixWord ++ tailWord_4372689) baseStart_4372689 baseEnd_4372689 := by
    simpa [prefixWord, tailWord_4372689, baseEnd_4372689] using wordTrace_append hprefix tailTrace_4372689
  have hstable : (prefixWord ++ tailWord_4372689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4372689).length < 2 ^ (prefixWord ++ tailWord_4372689).sum := by decide
  have hdescent : baseEnd_4372689 < baseStart_4372689 := by decide
  rcases family_descends (prefixWord ++ tailWord_4372689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4372696 : List Nat := [2, 1, 2, 2, 4, 2, 1, 1, 2, 6]
def baseStart_4372696 : Nat := 118140960795 + 4372696 * 2 ^ 59
def prefixEnd_4372696 : Nat := 4983230072969 + 3 ^ 40 * 4372696 * 2
def baseEnd_4372696 : Nat := 748431601330843013496781

theorem tailTrace_4372696 : CollatzResearch.WordTrace tailWord_4372696 prefixEnd_4372696 748431601330843013496781 := by
  unfold tailWord_4372696
  simp only [CollatzResearch.WordTrace]
  refine ⟨79742662683238331933180971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106323550244317775910907961 79742662683238331933180971)
  ·
    refine ⟨119613994024857497899771457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79742662683238331933180971 119613994024857497899771457)
    ·
      refine ⟨89710495518643123424828593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119613994024857497899771457 89710495518643123424828593)
      ·
        refine ⟨67282871638982342568621445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89710495518643123424828593 67282871638982342568621445)
        ·
          refine ⟨12615538432309189231616521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67282871638982342568621445 12615538432309189231616521)
          ·
            refine ⟨9461653824231891923712391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12615538432309189231616521 9461653824231891923712391)
            ·
              refine ⟨14192480736347837885568587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9461653824231891923712391 14192480736347837885568587)
              ·
                refine ⟨21288721104521756828352881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14192480736347837885568587 21288721104521756828352881)
                ·
                  refine ⟨15966540828391317621264661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21288721104521756828352881 15966540828391317621264661)
                  ·
                    refine ⟨748431601330843013496781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15966540828391317621264661 748431601330843013496781)
                    ·
                      rfl

theorem cell23_4372696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 2, 6].length) (baseStart_4372696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4372696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4372696 prefixEnd_4372696 := by exact prefixLift 4372696
  have htrace : WordTrace (prefixWord ++ tailWord_4372696) baseStart_4372696 baseEnd_4372696 := by
    simpa [prefixWord, tailWord_4372696, baseEnd_4372696] using wordTrace_append hprefix tailTrace_4372696
  have hstable : (prefixWord ++ tailWord_4372696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4372696).length < 2 ^ (prefixWord ++ tailWord_4372696).sum := by decide
  have hdescent : baseEnd_4372696 < baseStart_4372696 := by decide
  rcases family_descends (prefixWord ++ tailWord_4372696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4372699 : List Nat := [1, 1, 1, 1, 1, 1, 1, 7, 1, 4, 4]
def baseStart_4372699 : Nat := 118140960795 + 4372699 * 2 ^ 59
def prefixEnd_4372699 : Nat := 4983230072969 + 3 ^ 40 * 4372699 * 2
def baseEnd_4372699 : Nat := 2245296344434492528752829

theorem tailTrace_4372699 : CollatzResearch.WordTrace tailWord_4372699 prefixEnd_4372699 2245296344434492528752829 := by
  unfold tailWord_4372699
  simp only [CollatzResearch.WordTrace]
  refine ⟨159485434785465795378721151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106323623190310530252480767 159485434785465795378721151)
  ·
    refine ⟨239228152178198693068081727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159485434785465795378721151 239228152178198693068081727)
    ·
      refine ⟨358842228267298039602122591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239228152178198693068081727 358842228267298039602122591)
      ·
        refine ⟨538263342400947059403183887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 358842228267298039602122591 538263342400947059403183887)
        ·
          refine ⟨807395013601420589104775831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 538263342400947059403183887 807395013601420589104775831)
          ·
            refine ⟨1211092520402130883657163747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 807395013601420589104775831 1211092520402130883657163747)
            ·
              refine ⟨1816638780603196325485745621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1211092520402130883657163747 1816638780603196325485745621)
              ·
                refine ⟨42577471420387413878572163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1816638780603196325485745621 42577471420387413878572163)
                ·
                  refine ⟨63866207130581120817858245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42577471420387413878572163 63866207130581120817858245)
                  ·
                    refine ⟨11974913836983960153348421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 63866207130581120817858245 11974913836983960153348421)
                    ·
                      refine ⟨2245296344434492528752829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11974913836983960153348421 2245296344434492528752829)
                      ·
                        rfl

theorem cell23_4372699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 4, 4].length) (baseStart_4372699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4372699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4372699 prefixEnd_4372699 := by exact prefixLift 4372699
  have htrace : WordTrace (prefixWord ++ tailWord_4372699) baseStart_4372699 baseEnd_4372699 := by
    simpa [prefixWord, tailWord_4372699, baseEnd_4372699] using wordTrace_append hprefix tailTrace_4372699
  have hstable : (prefixWord ++ tailWord_4372699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4372699).length < 2 ^ (prefixWord ++ tailWord_4372699).sum := by decide
  have hdescent : baseEnd_4372699 < baseStart_4372699 := by decide
  rcases family_descends (prefixWord ++ tailWord_4372699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4372703 : List Nat := [1, 1, 2, 3, 2, 1, 1, 2, 6, 2, 2]
def baseStart_4372703 : Nat := 118140960795 + 4372703 * 2 ^ 59
def prefixEnd_4372703 : Nat := 4983230072969 + 3 ^ 40 * 4372703 * 2
def baseEnd_4372703 : Nat := 2245298398357110513102811

theorem tailTrace_4372703 : CollatzResearch.WordTrace tailWord_4372703 prefixEnd_4372703 2245298398357110513102811 := by
  unfold tailWord_4372703
  simp only [CollatzResearch.WordTrace]
  refine ⟨159485580677451304061866763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106323720451634202707911175 159485580677451304061866763)
  ·
    refine ⟨239228371016176956092800145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159485580677451304061866763 239228371016176956092800145)
    ·
      refine ⟨179421278262132717069600109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 239228371016176956092800145 179421278262132717069600109)
      ·
        refine ⟨67282979348299768901100041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 179421278262132717069600109 67282979348299768901100041)
        ·
          refine ⟨50462234511224826675825031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67282979348299768901100041 50462234511224826675825031)
          ·
            refine ⟨75693351766837240013737547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50462234511224826675825031 75693351766837240013737547)
            ·
              refine ⟨113540027650255860020606321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75693351766837240013737547 113540027650255860020606321)
              ·
                refine ⟨85155020737691895015454741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113540027650255860020606321 85155020737691895015454741)
                ·
                  refine ⟨3991641597079307578849441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 85155020737691895015454741 3991641597079307578849441)
                  ·
                    refine ⟨2993731197809480684137081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3991641597079307578849441 2993731197809480684137081)
                    ·
                      refine ⟨2245298398357110513102811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2993731197809480684137081 2245298398357110513102811)
                      ·
                        rfl

theorem cell23_4372703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 6, 2, 2].length) (baseStart_4372703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4372703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4372703 prefixEnd_4372703 := by exact prefixLift 4372703
  have htrace : WordTrace (prefixWord ++ tailWord_4372703) baseStart_4372703 baseEnd_4372703 := by
    simpa [prefixWord, tailWord_4372703, baseEnd_4372703] using wordTrace_append hprefix tailTrace_4372703
  have hstable : (prefixWord ++ tailWord_4372703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4372703).length < 2 ^ (prefixWord ++ tailWord_4372703).sum := by decide
  have hdescent : baseEnd_4372703 < baseStart_4372703 := by decide
  rcases family_descends (prefixWord ++ tailWord_4372703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4372736 : List Nat := [2, 1, 1, 2, 1, 1, 5, 2, 2, 3, 3]
def baseStart_4372736 : Nat := 118140960795 + 4372736 * 2 ^ 59
def prefixEnd_4372736 : Nat := 4983230072969 + 3 ^ 40 * 4372736 * 2
def baseEnd_4372736 : Nat := 2245315343218708883990159

theorem tailTrace_4372736 : CollatzResearch.WordTrace tailWord_4372736 prefixEnd_4372736 2245315343218708883990159 := by
  unfold tailWord_4372736
  simp only [CollatzResearch.WordTrace]
  refine ⟨79743392143165875348909031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106324522857554500465212041 79743392143165875348909031)
  ·
    refine ⟨119615088214748813023363547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79743392143165875348909031 119615088214748813023363547)
    ·
      refine ⟨179422632322123219535045321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119615088214748813023363547 179422632322123219535045321)
      ·
        refine ⟨134566974241592414651283991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179422632322123219535045321 134566974241592414651283991)
        ·
          refine ⟨201850461362388621976925987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134566974241592414651283991 201850461362388621976925987)
          ·
            refine ⟨302775692043582932965388981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201850461362388621976925987 302775692043582932965388981)
            ·
              refine ⟨28385221129085899965505217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 302775692043582932965388981 28385221129085899965505217)
              ·
                refine ⟨21288915846814424974128913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28385221129085899965505217 21288915846814424974128913)
                ·
                  refine ⟨15966686885110818730596685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21288915846814424974128913 15966686885110818730596685)
                  ·
                    refine ⟨5987507581916557023973757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15966686885110818730596685 5987507581916557023973757)
                    ·
                      refine ⟨2245315343218708883990159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5987507581916557023973757 2245315343218708883990159)
                      ·
                        rfl

theorem cell23_4372736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 2, 3, 3].length) (baseStart_4372736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4372736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4372736 prefixEnd_4372736 := by exact prefixLift 4372736
  have htrace : WordTrace (prefixWord ++ tailWord_4372736) baseStart_4372736 baseEnd_4372736 := by
    simpa [prefixWord, tailWord_4372736, baseEnd_4372736] using wordTrace_append hprefix tailTrace_4372736
  have hstable : (prefixWord ++ tailWord_4372736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4372736).length < 2 ^ (prefixWord ++ tailWord_4372736).sum := by decide
  have hdescent : baseEnd_4372736 < baseStart_4372736 := by decide
  rcases family_descends (prefixWord ++ tailWord_4372736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4372779 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 11]
def baseStart_4372779 : Nat := 118140960795 + 4372779 * 2 ^ 59
def prefixEnd_4372779 : Nat := 4983230072969 + 3 ^ 40 * 4372779 * 2
def baseEnd_4372779 : Nat := 2245337422886852215752461

theorem tailTrace_4372779 : CollatzResearch.WordTrace tailWord_4372779 prefixEnd_4372779 2245337422886852215752461 := by
  unfold tailWord_4372779
  simp only [CollatzResearch.WordTrace]
  refine ⟨159488352625175969041633391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106325568416783979361088927 159488352625175969041633391)
  ·
    refine ⟨239232528937763953562450087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159488352625175969041633391 239232528937763953562450087)
    ·
      refine ⟨358848793406645930343675131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239232528937763953562450087 358848793406645930343675131)
      ·
        refine ⟨538273190109968895515512697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 358848793406645930343675131 538273190109968895515512697)
        ·
          refine ⟨403704892582476671636634523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 538273190109968895515512697 403704892582476671636634523)
          ·
            refine ⟨605557338873715007454951785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 403704892582476671636634523 605557338873715007454951785)
            ·
              refine ⟨454168004155286255591213839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 605557338873715007454951785 454168004155286255591213839)
              ·
                refine ⟨681252006232929383386820759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 454168004155286255591213839 681252006232929383386820759)
                ·
                  refine ⟨1021878009349394075080231139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 681252006232929383386820759 1021878009349394075080231139)
                  ·
                    refine ⟨1532817014024091112620346709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1021878009349394075080231139 1532817014024091112620346709)
                    ·
                      refine ⟨2245337422886852215752461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 11 1532817014024091112620346709 2245337422886852215752461)
                      ·
                        rfl

theorem cell23_4372779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 11].length) (baseStart_4372779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4372779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4372779 prefixEnd_4372779 := by exact prefixLift 4372779
  have htrace : WordTrace (prefixWord ++ tailWord_4372779) baseStart_4372779 baseEnd_4372779 := by
    simpa [prefixWord, tailWord_4372779, baseEnd_4372779] using wordTrace_append hprefix tailTrace_4372779
  have hstable : (prefixWord ++ tailWord_4372779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4372779).length < 2 ^ (prefixWord ++ tailWord_4372779).sum := by decide
  have hdescent : baseEnd_4372779 < baseStart_4372779 := by decide
  rcases family_descends (prefixWord ++ tailWord_4372779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4372793 : List Nat := [1, 2, 1, 6, 1, 1, 1, 1, 4, 1, 4]
def baseStart_4372793 : Nat := 118140960795 + 4372793 * 2 ^ 59
def prefixEnd_4372793 : Nat := 4983230072969 + 3 ^ 40 * 4372793 * 2
def baseEnd_4372793 : Nat := 2245344611616015160977397

theorem tailTrace_4372793 : CollatzResearch.WordTrace tailWord_4372793 prefixEnd_4372793 2245344611616015160977397 := by
  unfold tailWord_4372793
  simp only [CollatzResearch.WordTrace]
  refine ⟨159488863247125249432643033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106325908831416832955095355 159488863247125249432643033)
  ·
    refine ⟨119616647435343937074482275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159488863247125249432643033 119616647435343937074482275)
    ·
      refine ⟨179424971153015905611723413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119616647435343937074482275 179424971153015905611723413)
      ·
        refine ⟨8410545522797620575549535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 179424971153015905611723413 8410545522797620575549535)
        ·
          refine ⟨12615818284196430863324303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8410545522797620575549535 12615818284196430863324303)
          ·
            refine ⟨18923727426294646294986455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12615818284196430863324303 18923727426294646294986455)
            ·
              refine ⟨28385591139441969442479683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18923727426294646294986455 28385591139441969442479683)
              ·
                refine ⟨42578386709162954163719525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28385591139441969442479683 42578386709162954163719525)
                ·
                  refine ⟨7983447507968053905697411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42578386709162954163719525 7983447507968053905697411)
                  ·
                    refine ⟨11975171261952080858546117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7983447507968053905697411 11975171261952080858546117)
                    ·
                      refine ⟨2245344611616015160977397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11975171261952080858546117 2245344611616015160977397)
                      ·
                        rfl

theorem cell23_4372793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_4372793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4372793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4372793 prefixEnd_4372793 := by exact prefixLift 4372793
  have htrace : WordTrace (prefixWord ++ tailWord_4372793) baseStart_4372793 baseEnd_4372793 := by
    simpa [prefixWord, tailWord_4372793, baseEnd_4372793] using wordTrace_append hprefix tailTrace_4372793
  have hstable : (prefixWord ++ tailWord_4372793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4372793).length < 2 ^ (prefixWord ++ tailWord_4372793).sum := by decide
  have hdescent : baseEnd_4372793 < baseStart_4372793 := by decide
  rcases family_descends (prefixWord ++ tailWord_4372793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4372803 : List Nat := [1, 1, 1, 3, 1, 3, 5, 1, 3, 4]
def baseStart_4372803 : Nat := 118140960795 + 4372803 * 2 ^ 59
def prefixEnd_4372803 : Nat := 4983230072969 + 3 ^ 40 * 4372803 * 2
def baseEnd_4372803 : Nat := 748449915474186707284117

theorem tailTrace_4372803 : CollatzResearch.WordTrace tailWord_4372803 prefixEnd_4372803 748449915474186707284117 := by
  unfold tailWord_4372803
  simp only [CollatzResearch.WordTrace]
  refine ⟨159489227977089021140507063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106326151984726014093671375 159489227977089021140507063)
  ·
    refine ⟨239233841965633531710760595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159489227977089021140507063 239233841965633531710760595)
    ·
      refine ⟨358850762948450297566140893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239233841965633531710760595 358850762948450297566140893)
      ·
        refine ⟨134569036105668861587302835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 358850762948450297566140893 134569036105668861587302835)
        ·
          refine ⟨201853554158503292380954253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134569036105668861587302835 201853554158503292380954253)
          ·
            refine ⟨75695082809438734642857845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 201853554158503292380954253 75695082809438734642857845)
            ·
              refine ⟨7096414013384881372767923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 75695082809438734642857845 7096414013384881372767923)
              ·
                refine ⟨10644621020077322059151885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7096414013384881372767923 10644621020077322059151885)
                ·
                  refine ⟨3991732882528995772181957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10644621020077322059151885 3991732882528995772181957)
                  ·
                    refine ⟨748449915474186707284117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3991732882528995772181957 748449915474186707284117)
                    ·
                      rfl

theorem cell23_4372803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 1, 3, 4].length) (baseStart_4372803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4372803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4372803 prefixEnd_4372803 := by exact prefixLift 4372803
  have htrace : WordTrace (prefixWord ++ tailWord_4372803) baseStart_4372803 baseEnd_4372803 := by
    simpa [prefixWord, tailWord_4372803, baseEnd_4372803] using wordTrace_append hprefix tailTrace_4372803
  have hstable : (prefixWord ++ tailWord_4372803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4372803).length < 2 ^ (prefixWord ++ tailWord_4372803).sum := by decide
  have hdescent : baseEnd_4372803 < baseStart_4372803 := by decide
  rcases family_descends (prefixWord ++ tailWord_4372803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4372843 : List Nat := [1, 1, 1, 1, 2, 2, 2, 4, 5, 1, 3]
def baseStart_4372843 : Nat := 118140960795 + 4372843 * 2 ^ 59
def prefixEnd_4372843 : Nat := 4983230072969 + 3 ^ 40 * 4372843 * 2
def baseEnd_4372843 : Nat := 2245370285648739965352167

theorem tailTrace_4372843 : CollatzResearch.WordTrace tailWord_4372843 prefixEnd_4372843 2245370285648739965352167 := by
  unfold tailWord_4372843
  simp only [CollatzResearch.WordTrace]
  refine ⟨159490686896944107971963183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106327124597962738647975455 159490686896944107971963183)
  ·
    refine ⟨239236030345416161957944775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159490686896944107971963183 239236030345416161957944775)
    ·
      refine ⟨358854045518124242936917163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239236030345416161957944775 358854045518124242936917163)
      ·
        refine ⟨538281068277186364405375745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 358854045518124242936917163 538281068277186364405375745)
        ·
          refine ⟨403710801207889773304031809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 538281068277186364405375745 403710801207889773304031809)
          ·
            refine ⟨302783100905917329978023857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 403710801207889773304031809 302783100905917329978023857)
            ·
              refine ⟨227087325679437997483517893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 302783100905917329978023857 227087325679437997483517893)
              ·
                refine ⟨42578873564894624528159605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 227087325679437997483517893 42578873564894624528159605)
                ·
                  refine ⟨3991769396708871049514963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42578873564894624528159605 3991769396708871049514963)
                  ·
                    refine ⟨5987654095063306574272445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3991769396708871049514963 5987654095063306574272445)
                    ·
                      refine ⟨2245370285648739965352167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5987654095063306574272445 2245370285648739965352167)
                      ·
                        rfl

theorem cell23_4372843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 5, 1, 3].length) (baseStart_4372843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4372843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4372843 prefixEnd_4372843 := by exact prefixLift 4372843
  have htrace : WordTrace (prefixWord ++ tailWord_4372843) baseStart_4372843 baseEnd_4372843 := by
    simpa [prefixWord, tailWord_4372843, baseEnd_4372843] using wordTrace_append hprefix tailTrace_4372843
  have hstable : (prefixWord ++ tailWord_4372843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4372843).length < 2 ^ (prefixWord ++ tailWord_4372843).sum := by decide
  have hdescent : baseEnd_4372843 < baseStart_4372843 := by decide
  rcases family_descends (prefixWord ++ tailWord_4372843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4372897 : List Nat := [1, 2, 3, 5, 1, 1, 1, 3, 1, 5]
def baseStart_4372897 : Nat := 118140960795 + 4372897 * 2 ^ 59
def prefixEnd_4372897 : Nat := 4983230072969 + 3 ^ 40 * 4372897 * 2
def baseEnd_4372897 : Nat := 748466004534694251358973

theorem tailTrace_4372897 : CollatzResearch.WordTrace tailWord_4372897 prefixEnd_4372897 748466004534694251358973 := by
  unfold tailWord_4372897
  simp only [CollatzResearch.WordTrace]
  refine ⟨159492656438748475194428945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106328437625832316796285963 159492656438748475194428945)
  ·
    refine ⟨119619492329061356395821709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159492656438748475194428945 119619492329061356395821709)
    ·
      refine ⟨44857309623398008648433141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119619492329061356395821709 44857309623398008648433141)
      ·
        refine ⟨4205372777193563310790607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44857309623398008648433141 4205372777193563310790607)
        ·
          refine ⟨6308059165790344966185911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4205372777193563310790607 6308059165790344966185911)
          ·
            refine ⟨9462088748685517449278867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6308059165790344966185911 9462088748685517449278867)
            ·
              refine ⟨14193133123028276173918301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9462088748685517449278867 14193133123028276173918301)
              ·
                refine ⟨5322424921135603565219363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14193133123028276173918301 5322424921135603565219363)
                ·
                  refine ⟨7983637381703405347829045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5322424921135603565219363 7983637381703405347829045)
                  ·
                    refine ⟨748466004534694251358973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7983637381703405347829045 748466004534694251358973)
                    ·
                      rfl

theorem cell23_4372897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 3, 1, 5].length) (baseStart_4372897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4372897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4372897 prefixEnd_4372897 := by exact prefixLift 4372897
  have htrace : WordTrace (prefixWord ++ tailWord_4372897) baseStart_4372897 baseEnd_4372897 := by
    simpa [prefixWord, tailWord_4372897, baseEnd_4372897] using wordTrace_append hprefix tailTrace_4372897
  have hstable : (prefixWord ++ tailWord_4372897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4372897).length < 2 ^ (prefixWord ++ tailWord_4372897).sum := by decide
  have hdescent : baseEnd_4372897 < baseStart_4372897 := by decide
  rcases family_descends (prefixWord ++ tailWord_4372897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4372967 : List Nat := [1, 1, 5, 2, 1, 1, 2, 4, 2, 1, 3]
def baseStart_4372967 : Nat := 118140960795 + 4372967 * 2 ^ 59
def prefixEnd_4372967 : Nat := 4983230072969 + 3 ^ 40 * 4372967 * 2
def baseEnd_4372967 : Nat := 2245433957249897480201597

theorem tailTrace_4372967 : CollatzResearch.WordTrace tailWord_4372967 prefixEnd_4372967 2245433957249897480201597 := by
  unfold tailWord_4372967
  simp only [CollatzResearch.WordTrace]
  refine ⟨159495209548494877149477155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106330139698996584766318103 159495209548494877149477155)
  ·
    refine ⟨239242814322742315724215733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159495209548494877149477155 239242814322742315724215733)
    ·
      refine ⟨22429013842757092099145225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 239242814322742315724215733 22429013842757092099145225)
      ·
        refine ⟨16821760382067819074358919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22429013842757092099145225 16821760382067819074358919)
        ·
          refine ⟨25232640573101728611538379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16821760382067819074358919 25232640573101728611538379)
          ·
            refine ⟨37848960859652592917307569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25232640573101728611538379 37848960859652592917307569)
            ·
              refine ⟨28386720644739444687980677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37848960859652592917307569 28386720644739444687980677)
              ·
                refine ⟨5322510120888645878996377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28386720644739444687980677 5322510120888645878996377)
                ·
                  refine ⟨3991882590666484409247283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5322510120888645878996377 3991882590666484409247283)
                  ·
                    refine ⟨5987823885999726613870925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3991882590666484409247283 5987823885999726613870925)
                    ·
                      refine ⟨2245433957249897480201597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5987823885999726613870925 2245433957249897480201597)
                      ·
                        rfl

theorem cell23_4372967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_4372967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4372967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4372967 prefixEnd_4372967 := by exact prefixLift 4372967
  have htrace : WordTrace (prefixWord ++ tailWord_4372967) baseStart_4372967 baseEnd_4372967 := by
    simpa [prefixWord, tailWord_4372967, baseEnd_4372967] using wordTrace_append hprefix tailTrace_4372967
  have hstable : (prefixWord ++ tailWord_4372967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4372967).length < 2 ^ (prefixWord ++ tailWord_4372967).sum := by decide
  have hdescent : baseEnd_4372967 < baseStart_4372967 := by decide
  rcases family_descends (prefixWord ++ tailWord_4372967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4373043 : List Nat := [1, 1, 1, 2, 4, 2, 2, 2, 1, 7]
def baseStart_4373043 : Nat := 118140960795 + 4373043 * 2 ^ 59
def prefixEnd_4373043 : Nat := 4983230072969 + 3 ^ 40 * 4373043 * 2
def baseEnd_4373043 : Nat := 748490993926546394283749

theorem tailTrace_4373043 : CollatzResearch.WordTrace tailWord_4373043 prefixEnd_4373043 748490993926546394283749 := by
  unfold tailWord_4373043
  simp only [CollatzResearch.WordTrace]
  refine ⟨159497981496219542129243783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106331987664146361419495855 159497981496219542129243783)
  ·
    refine ⟨239246972244329313193865675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159497981496219542129243783 239246972244329313193865675)
    ·
      refine ⟨358870458366493969790798513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239246972244329313193865675 358870458366493969790798513)
      ·
        refine ⟨269152843774870477343098885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 358870458366493969790798513 269152843774870477343098885)
        ·
          refine ⟨50466158207788214501831041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 269152843774870477343098885 50466158207788214501831041)
          ·
            refine ⟨37849618655841160876373281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50466158207788214501831041 37849618655841160876373281)
            ·
              refine ⟨28387213991880870657279961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37849618655841160876373281 28387213991880870657279961)
              ·
                refine ⟨21290410493910652992959971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28387213991880870657279961 21290410493910652992959971)
                ·
                  refine ⟨31935615740865979489439957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21290410493910652992959971 31935615740865979489439957)
                  ·
                    refine ⟨748490993926546394283749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31935615740865979489439957 748490993926546394283749)
                    ·
                      rfl

theorem cell23_4373043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 7].length) (baseStart_4373043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4373043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4373043 prefixEnd_4373043 := by exact prefixLift 4373043
  have htrace : WordTrace (prefixWord ++ tailWord_4373043) baseStart_4373043 baseEnd_4373043 := by
    simpa [prefixWord, tailWord_4373043, baseEnd_4373043] using wordTrace_append hprefix tailTrace_4373043
  have hstable : (prefixWord ++ tailWord_4373043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4373043).length < 2 ^ (prefixWord ++ tailWord_4373043).sum := by decide
  have hdescent : baseEnd_4373043 < baseStart_4373043 := by decide
  rcases family_descends (prefixWord ++ tailWord_4373043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4373080 : List Nat := [2, 1, 2, 2, 1, 2, 2, 4, 2, 1, 4]
def baseStart_4373080 : Nat := 118140960795 + 4373080 * 2 ^ 59
def prefixEnd_4373080 : Nat := 4983230072969 + 3 ^ 40 * 4373080 * 2
def baseEnd_4373080 : Nat := 2245491980563855538088577

theorem tailTrace_4373080 : CollatzResearch.WordTrace tailWord_4373080 prefixEnd_4373080 2245491980563855538088577 := by
  unfold tailWord_4373080
  simp only [CollatzResearch.WordTrace]
  refine ⟨79749665498542748724170347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106332887331390331632227129 79749665498542748724170347)
  ·
    refine ⟨119624498247814123086255521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79749665498542748724170347 119624498247814123086255521)
    ·
      refine ⟨89718373685860592314691641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119624498247814123086255521 89718373685860592314691641)
      ·
        refine ⟨67288780264395444236018731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89718373685860592314691641 67288780264395444236018731)
        ·
          refine ⟨100933170396593166354028097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67288780264395444236018731 100933170396593166354028097)
          ·
            refine ⟨75699877797444874765521073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100933170396593166354028097 75699877797444874765521073)
            ·
              refine ⟨56774908348083656074140805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75699877797444874765521073 56774908348083656074140805)
              ·
                refine ⟨10645295315265685513901401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56774908348083656074140805 10645295315265685513901401)
                ·
                  refine ⟨7983971486449264135426051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10645295315265685513901401 7983971486449264135426051)
                  ·
                    refine ⟨11975957229673896203139077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7983971486449264135426051 11975957229673896203139077)
                    ·
                      refine ⟨2245491980563855538088577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11975957229673896203139077 2245491980563855538088577)
                      ·
                        rfl

theorem cell23_4373080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 4, 2, 1, 4].length) (baseStart_4373080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4373080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4373080 prefixEnd_4373080 := by exact prefixLift 4373080
  have htrace : WordTrace (prefixWord ++ tailWord_4373080) baseStart_4373080 baseEnd_4373080 := by
    simpa [prefixWord, tailWord_4373080, baseEnd_4373080] using wordTrace_append hprefix tailTrace_4373080
  have hstable : (prefixWord ++ tailWord_4373080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4373080).length < 2 ^ (prefixWord ++ tailWord_4373080).sum := by decide
  have hdescent : baseEnd_4373080 < baseStart_4373080 := by decide
  rcases family_descends (prefixWord ++ tailWord_4373080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4373100 : List Nat := [2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 3]
def baseStart_4373100 : Nat := 118140960795 + 4373100 * 2 ^ 59
def prefixEnd_4373100 : Nat := 4983230072969 + 3 ^ 40 * 4373100 * 2
def baseEnd_4373100 : Nat := 2245502250176945459838485

theorem tailTrace_4373100 : CollatzResearch.WordTrace tailWord_4373100 prefixEnd_4373100 2245502250176945459838485 := by
  unfold tailWord_4373100
  simp only [CollatzResearch.WordTrace]
  refine ⟨79750030228506520432034377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106333373638008693909379169 79750030228506520432034377)
  ·
    refine ⟨59812522671379890324025783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79750030228506520432034377 59812522671379890324025783)
    ·
      refine ⟨89718784007069835486038675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59812522671379890324025783 89718784007069835486038675)
      ·
        refine ⟨134578176010604753229058013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89718784007069835486038675 134578176010604753229058013)
        ·
          refine ⟨50466816003976782460896755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134578176010604753229058013 50466816003976782460896755)
          ·
            refine ⟨75700224005965173691345133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50466816003976782460896755 75700224005965173691345133)
            ·
              refine ⟨28387584002236940134254425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75700224005965173691345133 28387584002236940134254425)
              ·
                refine ⟨21290688001677705100690819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28387584002236940134254425 21290688001677705100690819)
                ·
                  refine ⟨31936032002516557651036229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21290688001677705100690819 31936032002516557651036229)
                  ·
                    refine ⟨5988006000471854559569293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31936032002516557651036229 5988006000471854559569293)
                    ·
                      refine ⟨2245502250176945459838485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5988006000471854559569293 2245502250176945459838485)
                      ·
                        rfl

theorem cell23_4373100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 3].length) (baseStart_4373100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4373100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4373100 prefixEnd_4373100 := by exact prefixLift 4373100
  have htrace : WordTrace (prefixWord ++ tailWord_4373100) baseStart_4373100 baseEnd_4373100 := by
    simpa [prefixWord, tailWord_4373100, baseEnd_4373100] using wordTrace_append hprefix tailTrace_4373100
  have hstable : (prefixWord ++ tailWord_4373100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4373100).length < 2 ^ (prefixWord ++ tailWord_4373100).sum := by decide
  have hdescent : baseEnd_4373100 < baseStart_4373100 := by decide
  rcases family_descends (prefixWord ++ tailWord_4373100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4373157 : List Nat := [1, 3, 1, 2, 1, 2, 1, 1, 6, 3, 2]
def baseStart_4373157 : Nat := 118140960795 + 4373157 * 2 ^ 59
def prefixEnd_4373157 : Nat := 4983230072969 + 3 ^ 40 * 4373157 * 2
def baseEnd_4373157 : Nat := 2245531518574251736825723

theorem tailTrace_4373157 : CollatzResearch.WordTrace tailWord_4373157 prefixEnd_4373157 2245531518574251736825723 := by
  unfold tailWord_4373157
  simp only [CollatzResearch.WordTrace]
  refine ⟨159502139417806539598893725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106334759611871026399262483 159502139417806539598893725)
  ·
    refine ⟨59813302281677452349585147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159502139417806539598893725 59813302281677452349585147)
    ·
      refine ⟨89719953422516178524377721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59813302281677452349585147 89719953422516178524377721)
      ·
        refine ⟨67289965066887133893283291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89719953422516178524377721 67289965066887133893283291)
        ·
          refine ⟨100934947600330700839924937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67289965066887133893283291 100934947600330700839924937)
          ·
            refine ⟨75701210700248025629943703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100934947600330700839924937 75701210700248025629943703)
            ·
              refine ⟨113551816050372038444915555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75701210700248025629943703 113551816050372038444915555)
              ·
                refine ⟨170327724075558057667373333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113551816050372038444915555 170327724075558057667373333)
                ·
                  refine ⟨7984112066041783953158125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 170327724075558057667373333 7984112066041783953158125)
                  ·
                    refine ⟨2994042024765668982434297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7984112066041783953158125 2994042024765668982434297)
                    ·
                      refine ⟨2245531518574251736825723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2994042024765668982434297 2245531518574251736825723)
                      ·
                        rfl

theorem cell23_4373157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 6, 3, 2].length) (baseStart_4373157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4373157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4373157 prefixEnd_4373157 := by exact prefixLift 4373157
  have htrace : WordTrace (prefixWord ++ tailWord_4373157) baseStart_4373157 baseEnd_4373157 := by
    simpa [prefixWord, tailWord_4373157, baseEnd_4373157] using wordTrace_append hprefix tailTrace_4373157
  have hstable : (prefixWord ++ tailWord_4373157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4373157).length < 2 ^ (prefixWord ++ tailWord_4373157).sum := by decide
  have hdescent : baseEnd_4373157 < baseStart_4373157 := by decide
  rcases family_descends (prefixWord ++ tailWord_4373157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4373167 : List Nat := [1, 1, 2, 1, 2, 5, 3, 2, 1, 5]
def baseStart_4373167 : Nat := 118140960795 + 4373167 * 2 ^ 59
def prefixEnd_4373167 : Nat := 4983230072969 + 3 ^ 40 * 4373167 * 2
def baseEnd_4373167 : Nat := 748512217793598899233559

theorem tailTrace_4373167 : CollatzResearch.WordTrace tailWord_4373167 prefixEnd_4373167 748512217793598899233559 := by
  unfold tailWord_4373167
  simp only [CollatzResearch.WordTrace]
  refine ⟨159502504147770311306757755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106335002765180207537838503 159502504147770311306757755)
  ·
    refine ⟨239253756221655466960136633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159502504147770311306757755 239253756221655466960136633)
    ·
      refine ⟨179440317166241600220102475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 239253756221655466960136633 179440317166241600220102475)
      ·
        refine ⟨269160475749362400330153713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179440317166241600220102475 269160475749362400330153713)
        ·
          refine ⟨201870356812021800247615285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 269160475749362400330153713 201870356812021800247615285)
          ·
            refine ⟨18925345951127043773213933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 201870356812021800247615285 18925345951127043773213933)
            ·
              refine ⟨7097004731672641414955225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18925345951127043773213933 7097004731672641414955225)
              ·
                refine ⟨5322753548754481061216419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7097004731672641414955225 5322753548754481061216419)
                ·
                  refine ⟨7984130323131721591824629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5322753548754481061216419 7984130323131721591824629)
                  ·
                    refine ⟨748512217793598899233559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7984130323131721591824629 748512217793598899233559)
                    ·
                      rfl

theorem cell23_4373167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 2, 1, 5].length) (baseStart_4373167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4373167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4373167 prefixEnd_4373167 := by exact prefixLift 4373167
  have htrace : WordTrace (prefixWord ++ tailWord_4373167) baseStart_4373167 baseEnd_4373167 := by
    simpa [prefixWord, tailWord_4373167, baseEnd_4373167] using wordTrace_append hprefix tailTrace_4373167
  have hstable : (prefixWord ++ tailWord_4373167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4373167).length < 2 ^ (prefixWord ++ tailWord_4373167).sum := by decide
  have hdescent : baseEnd_4373167 < baseStart_4373167 := by decide
  rcases family_descends (prefixWord ++ tailWord_4373167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4373184 : List Nat := [2, 1, 1, 2, 4, 3, 3, 1, 1, 5]
def baseStart_4373184 : Nat := 118140960795 + 4373184 * 2 ^ 59
def prefixEnd_4373184 : Nat := 4983230072969 + 3 ^ 40 * 4373184 * 2
def baseEnd_4373184 : Nat := 748515127517307710396033

theorem tailTrace_4373184 : CollatzResearch.WordTrace tailWord_4373184 prefixEnd_4373184 748515127517307710396033 := by
  unfold tailWord_4373184
  simp only [CollatzResearch.WordTrace]
  refine ⟨79751562094354361605063303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106335416125805815473417737 79751562094354361605063303)
  ·
    refine ⟨119627343141531542407594955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79751562094354361605063303 119627343141531542407594955)
    ·
      refine ⟨179441014712297313611392433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119627343141531542407594955 179441014712297313611392433)
      ·
        refine ⟨134580761034222985208544325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179441014712297313611392433 134580761034222985208544325)
        ·
          refine ⟨25233892693916809726602061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 134580761034222985208544325 25233892693916809726602061)
          ·
            refine ⟨9462709760218803647475773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25233892693916809726602061 9462709760218803647475773)
            ·
              refine ⟨3548516160082051367803415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9462709760218803647475773 3548516160082051367803415)
              ·
                refine ⟨5322774240123077051705123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3548516160082051367803415 5322774240123077051705123)
                ·
                  refine ⟨7984161360184615577557685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5322774240123077051705123 7984161360184615577557685)
                  ·
                    refine ⟨748515127517307710396033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7984161360184615577557685 748515127517307710396033)
                    ·
                      rfl

theorem cell23_4373184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 3, 1, 1, 5].length) (baseStart_4373184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4373184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4373184 prefixEnd_4373184 := by exact prefixLift 4373184
  have htrace : WordTrace (prefixWord ++ tailWord_4373184) baseStart_4373184 baseEnd_4373184 := by
    simpa [prefixWord, tailWord_4373184, baseEnd_4373184] using wordTrace_append hprefix tailTrace_4373184
  have hstable : (prefixWord ++ tailWord_4373184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4373184).length < 2 ^ (prefixWord ++ tailWord_4373184).sum := by decide
  have hdescent : baseEnd_4373184 < baseStart_4373184 := by decide
  rcases family_descends (prefixWord ++ tailWord_4373184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4373198 : List Nat := [4, 1, 1, 1, 3, 2, 4, 2, 1, 1, 3]
def baseStart_4373198 : Nat := 118140960795 + 4373198 * 2 ^ 59
def prefixEnd_4373198 : Nat := 4983230072969 + 3 ^ 40 * 4373198 * 2
def baseEnd_4373198 : Nat := 2245552571281086076413035

theorem tailTrace_4373198 : CollatzResearch.WordTrace tailWord_4373198 prefixEnd_4373198 2245552571281086076413035 := by
  unfold tailWord_4373198
  simp only [CollatzResearch.WordTrace]
  refine ⟨19937954351332250450142031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106335756540438669067424165 19937954351332250450142031)
  ·
    refine ⟨29906931526998375675213047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19937954351332250450142031 29906931526998375675213047)
    ·
      refine ⟨44860397290497563512819571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29906931526998375675213047 44860397290497563512819571)
      ·
        refine ⟨67290595935746345269229357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44860397290497563512819571 67290595935746345269229357)
        ·
          refine ⟨25233973475904879475961009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67290595935746345269229357 25233973475904879475961009)
          ·
            refine ⟨18925480106928659606970757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25233973475904879475961009 18925480106928659606970757)
            ·
              refine ⟨3548527520049123676307017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18925480106928659606970757 3548527520049123676307017)
              ·
                refine ⟨2661395640036842757230263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3548527520049123676307017 2661395640036842757230263)
                ·
                  refine ⟨3992093460055264135845395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2661395640036842757230263 3992093460055264135845395)
                  ·
                    refine ⟨5988140190082896203768093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3992093460055264135845395 5988140190082896203768093)
                    ·
                      refine ⟨2245552571281086076413035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5988140190082896203768093 2245552571281086076413035)
                      ·
                        rfl

theorem cell23_4373198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 4, 2, 1, 1, 3].length) (baseStart_4373198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4373198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4373198 prefixEnd_4373198 := by exact prefixLift 4373198
  have htrace : WordTrace (prefixWord ++ tailWord_4373198) baseStart_4373198 baseEnd_4373198 := by
    simpa [prefixWord, tailWord_4373198, baseEnd_4373198] using wordTrace_append hprefix tailTrace_4373198
  have hstable : (prefixWord ++ tailWord_4373198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4373198).length < 2 ^ (prefixWord ++ tailWord_4373198).sum := by decide
  have hdescent : baseEnd_4373198 < baseStart_4373198 := by decide
  rcases family_descends (prefixWord ++ tailWord_4373198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4373207 : List Nat := [1, 1, 3, 2, 1, 4, 1, 2, 3, 2, 3]
def baseStart_4373207 : Nat := 118140960795 + 4373207 * 2 ^ 59
def prefixEnd_4373207 : Nat := 4983230072969 + 3 ^ 40 * 4373207 * 2
def baseEnd_4373207 : Nat := 2245557192606976541200493

theorem tailTrace_4373207 : CollatzResearch.WordTrace tailWord_4373207 prefixEnd_4373207 2245557192606976541200493 := by
  unfold tailWord_4373207
  simp only [CollatzResearch.WordTrace]
  refine ⟨159503963067625398138213875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106335975378416932092142583 159503963067625398138213875)
  ·
    refine ⟨239255944601438097207320813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159503963067625398138213875 239255944601438097207320813)
    ·
      refine ⟨89720979225539286452745305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 239255944601438097207320813 89720979225539286452745305)
      ·
        refine ⟨67290734419154464839558979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89720979225539286452745305 67290734419154464839558979)
        ·
          refine ⟨100936101628731697259338469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67290734419154464839558979 100936101628731697259338469)
          ·
            refine ⟨18925519055387193236125963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 100936101628731697259338469 18925519055387193236125963)
            ·
              refine ⟨28388278583080789854188945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18925519055387193236125963 28388278583080789854188945)
              ·
                refine ⟨21291208937310592390641709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28388278583080789854188945 21291208937310592390641709)
                ·
                  refine ⟨7984203351491472146490641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21291208937310592390641709 7984203351491472146490641)
                  ·
                    refine ⟨5988152513618604109867981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7984203351491472146490641 5988152513618604109867981)
                    ·
                      refine ⟨2245557192606976541200493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5988152513618604109867981 2245557192606976541200493)
                      ·
                        rfl

theorem cell23_4373207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 3, 2, 3].length) (baseStart_4373207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4373207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4373207 prefixEnd_4373207 := by exact prefixLift 4373207
  have htrace : WordTrace (prefixWord ++ tailWord_4373207) baseStart_4373207 baseEnd_4373207 := by
    simpa [prefixWord, tailWord_4373207, baseEnd_4373207] using wordTrace_append hprefix tailTrace_4373207
  have hstable : (prefixWord ++ tailWord_4373207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4373207).length < 2 ^ (prefixWord ++ tailWord_4373207).sum := by decide
  have hdescent : baseEnd_4373207 < baseStart_4373207 := by decide
  rcases family_descends (prefixWord ++ tailWord_4373207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4373217 : List Nat := [1, 2, 3, 1, 4, 1, 1, 3, 1, 2, 4]
def baseStart_4373217 : Nat := 118140960795 + 4373217 * 2 ^ 59
def prefixEnd_4373217 : Nat := 4983230072969 + 3 ^ 40 * 4373217 * 2
def baseEnd_4373217 : Nat := 2245562327413521502075447

theorem tailTrace_4373217 : CollatzResearch.WordTrace tailWord_4373217 prefixEnd_4373217 2245562327413521502075447 := by
  unfold tailWord_4373217
  simp only [CollatzResearch.WordTrace]
  refine ⟨159504327797589169846077905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106336218531726113230718603 159504327797589169846077905)
  ·
    refine ⟨119628245848191877384558429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159504327797589169846077905 119628245848191877384558429)
    ·
      refine ⟨44860592193071954019209411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119628245848191877384558429 44860592193071954019209411)
      ·
        refine ⟨67290888289607931028814117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44860592193071954019209411 67290888289607931028814117)
        ·
          refine ⟨12617041554301487067902647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67290888289607931028814117 12617041554301487067902647)
          ·
            refine ⟨18925562331452230601853971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12617041554301487067902647 18925562331452230601853971)
            ·
              refine ⟨28388343497178345902780957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18925562331452230601853971 28388343497178345902780957)
              ·
                refine ⟨10645628811441879713542859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28388343497178345902780957 10645628811441879713542859)
                ·
                  refine ⟨15968443217162819570314289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10645628811441879713542859 15968443217162819570314289)
                  ·
                    refine ⟨11976332412872114677735717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15968443217162819570314289 11976332412872114677735717)
                    ·
                      refine ⟨2245562327413521502075447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11976332412872114677735717 2245562327413521502075447)
                      ·
                        rfl

theorem cell23_4373217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 3, 1, 2, 4].length) (baseStart_4373217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4373217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4373217 prefixEnd_4373217 := by exact prefixLift 4373217
  have htrace : WordTrace (prefixWord ++ tailWord_4373217) baseStart_4373217 baseEnd_4373217 := by
    simpa [prefixWord, tailWord_4373217, baseEnd_4373217] using wordTrace_append hprefix tailTrace_4373217
  have hstable : (prefixWord ++ tailWord_4373217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4373217).length < 2 ^ (prefixWord ++ tailWord_4373217).sum := by decide
  have hdescent : baseEnd_4373217 < baseStart_4373217 := by decide
  rcases family_descends (prefixWord ++ tailWord_4373217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4373221 : List Nat := [1, 3, 1, 4, 1, 3, 1, 2, 3, 2, 2]
def baseStart_4373221 : Nat := 118140960795 + 4373221 * 2 ^ 59
def prefixEnd_4373221 : Nat := 4983230072969 + 3 ^ 40 * 4373221 * 2
def baseEnd_4373221 : Nat := 2245564381336139486425429

theorem tailTrace_4373221 : CollatzResearch.WordTrace tailWord_4373221 prefixEnd_4373221 2245564381336139486425429 := by
  unfold tailWord_4373221
  simp only [CollatzResearch.WordTrace]
  refine ⟨159504473689574678529223517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106336315793049785686149011 159504473689574678529223517)
  ·
    refine ⟨59814177633590504448458819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159504473689574678529223517 59814177633590504448458819)
    ·
      refine ⟨89721266450385756672688229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59814177633590504448458819 89721266450385756672688229)
      ·
        refine ⟨16822737459447329376129043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 89721266450385756672688229 16822737459447329376129043)
        ·
          refine ⟨25234106189170994064193565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16822737459447329376129043 25234106189170994064193565)
          ·
            refine ⟨9462789820939122774072587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25234106189170994064193565 9462789820939122774072587)
            ·
              refine ⟨14194184731408684161108881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9462789820939122774072587 14194184731408684161108881)
              ·
                refine ⟨10645638548556513120831661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14194184731408684161108881 10645638548556513120831661)
                ·
                  refine ⟨3992114455708692420311873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10645638548556513120831661 3992114455708692420311873)
                  ·
                    refine ⟨2994085841781519315233905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3992114455708692420311873 2994085841781519315233905)
                    ·
                      refine ⟨2245564381336139486425429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2994085841781519315233905 2245564381336139486425429)
                      ·
                        rfl

theorem cell23_4373221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 2, 3, 2, 2].length) (baseStart_4373221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4373221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4373221 prefixEnd_4373221 := by exact prefixLift 4373221
  have htrace : WordTrace (prefixWord ++ tailWord_4373221) baseStart_4373221 baseEnd_4373221 := by
    simpa [prefixWord, tailWord_4373221, baseEnd_4373221] using wordTrace_append hprefix tailTrace_4373221
  have hstable : (prefixWord ++ tailWord_4373221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4373221).length < 2 ^ (prefixWord ++ tailWord_4373221).sum := by decide
  have hdescent : baseEnd_4373221 < baseStart_4373221 := by decide
  rcases family_descends (prefixWord ++ tailWord_4373221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4373271 : List Nat := [1, 1, 3, 4, 3, 2, 1, 1, 1, 3, 3]
def baseStart_4373271 : Nat := 118140960795 + 4373271 * 2 ^ 59
def prefixEnd_4373271 : Nat := 4983230072969 + 3 ^ 40 * 4373271 * 2
def baseEnd_4373271 : Nat := 2245590055368864290800199

theorem tailTrace_4373271 : CollatzResearch.WordTrace tailWord_4373271 prefixEnd_4373271 2245590055368864290800199 := by
  unfold tailWord_4373271
  simp only [CollatzResearch.WordTrace]
  refine ⟨159506297339393537068543667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106337531559595691379029111 159506297339393537068543667)
  ·
    refine ⟨239259446009090305602815501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159506297339393537068543667 239259446009090305602815501)
    ·
      refine ⟨89722292253408864601055813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 239259446009090305602815501 89722292253408864601055813)
      ·
        refine ⟨16822929797514162112697965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 89722292253408864601055813 16822929797514162112697965)
        ·
          refine ⟨6308598674067810792261737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16822929797514162112697965 6308598674067810792261737)
          ·
            refine ⟨4731449005550858094196303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6308598674067810792261737 4731449005550858094196303)
            ·
              refine ⟨7097173508326287141294455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4731449005550858094196303 7097173508326287141294455)
              ·
                refine ⟨10645760262489430711941683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7097173508326287141294455 10645760262489430711941683)
                ·
                  refine ⟨15968640393734146067912525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10645760262489430711941683 15968640393734146067912525)
                  ·
                    refine ⟨5988240147650304775467197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15968640393734146067912525 5988240147650304775467197)
                    ·
                      refine ⟨2245590055368864290800199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5988240147650304775467197 2245590055368864290800199)
                      ·
                        rfl

theorem cell23_4373271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_4373271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4373271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4373271 prefixEnd_4373271 := by exact prefixLift 4373271
  have htrace : WordTrace (prefixWord ++ tailWord_4373271) baseStart_4373271 baseEnd_4373271 := by
    simpa [prefixWord, tailWord_4373271, baseEnd_4373271] using wordTrace_append hprefix tailTrace_4373271
  have hstable : (prefixWord ++ tailWord_4373271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4373271).length < 2 ^ (prefixWord ++ tailWord_4373271).sum := by decide
  have hdescent : baseEnd_4373271 < baseStart_4373271 := by decide
  rcases family_descends (prefixWord ++ tailWord_4373271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4373281 : List Nat := [1, 2, 3, 2, 1, 2, 4, 2, 1, 3, 2]
def baseStart_4373281 : Nat := 118140960795 + 4373281 * 2 ^ 59
def prefixEnd_4373281 : Nat := 4983230072969 + 3 ^ 40 * 4373281 * 2
def baseEnd_4373281 : Nat := 2245595190175409251675153

theorem tailTrace_4373281 : CollatzResearch.WordTrace tailWord_4373281 prefixEnd_4373281 2245595190175409251675153 := by
  unfold tailWord_4373281
  simp only [CollatzResearch.WordTrace]
  refine ⟨159506662069357308776407697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106337774712904872517605131 159506662069357308776407697)
  ·
    refine ⟨119629996552017981582305773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159506662069357308776407697 119629996552017981582305773)
    ·
      refine ⟨44861248707006743093364665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119629996552017981582305773 44861248707006743093364665)
      ·
        refine ⟨33645936530255057320023499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44861248707006743093364665 33645936530255057320023499)
        ·
          refine ⟨50468904795382585980035249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33645936530255057320023499 50468904795382585980035249)
          ·
            refine ⟨37851678596536939485026437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50468904795382585980035249 37851678596536939485026437)
            ·
              refine ⟨7097189736850676153442457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37851678596536939485026437 7097189736850676153442457)
              ·
                refine ⟨5322892302638007115081843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7097189736850676153442457 5322892302638007115081843)
                ·
                  refine ⟨7984338453957010672622765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5322892302638007115081843 7984338453957010672622765)
                  ·
                    refine ⟨2994126920233879002233537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7984338453957010672622765 2994126920233879002233537)
                    ·
                      refine ⟨2245595190175409251675153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2994126920233879002233537 2245595190175409251675153)
                      ·
                        rfl

theorem cell23_4373281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 2, 1, 3, 2].length) (baseStart_4373281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4373281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4373281 prefixEnd_4373281 := by exact prefixLift 4373281
  have htrace : WordTrace (prefixWord ++ tailWord_4373281) baseStart_4373281 baseEnd_4373281 := by
    simpa [prefixWord, tailWord_4373281, baseEnd_4373281] using wordTrace_append hprefix tailTrace_4373281
  have hstable : (prefixWord ++ tailWord_4373281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4373281).length < 2 ^ (prefixWord ++ tailWord_4373281).sum := by decide
  have hdescent : baseEnd_4373281 < baseStart_4373281 := by decide
  rcases family_descends (prefixWord ++ tailWord_4373281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4373297 : List Nat := [1, 2, 2, 3, 2, 1, 3, 1, 2, 1, 5]
def baseStart_4373297 : Nat := 118140960795 + 4373297 * 2 ^ 59
def prefixEnd_4373297 : Nat := 4983230072969 + 3 ^ 40 * 4373297 * 2
def baseEnd_4373297 : Nat := 2245603405865881189075079

theorem tailTrace_4373297 : CollatzResearch.WordTrace tailWord_4373297 prefixEnd_4373297 2245603405865881189075079 := by
  unfold tailWord_4373297
  simp only [CollatzResearch.WordTrace]
  refine ⟨159507245637299343508990145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106338163758199562339326763 159507245637299343508990145)
  ·
    refine ⟨119630434227974507631742609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159507245637299343508990145 119630434227974507631742609)
    ·
      refine ⟨89722825670980880723806957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119630434227974507631742609 89722825670980880723806957)
      ·
        refine ⟨33646059626617830271427609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89722825670980880723806957 33646059626617830271427609)
        ·
          refine ⟨25234544719963372703570707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33646059626617830271427609 25234544719963372703570707)
          ·
            refine ⟨37851817079945059055356061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25234544719963372703570707 37851817079945059055356061)
            ·
              refine ⟨14194431404979397145758523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37851817079945059055356061 14194431404979397145758523)
              ·
                refine ⟨21291647107469095718637785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14194431404979397145758523 21291647107469095718637785)
                ·
                  refine ⟨15968735330601821788978339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21291647107469095718637785 15968735330601821788978339)
                  ·
                    refine ⟨23953102995902732683467509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15968735330601821788978339 23953102995902732683467509)
                    ·
                      refine ⟨2245603405865881189075079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23953102995902732683467509 2245603405865881189075079)
                      ·
                        rfl

theorem cell23_4373297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_4373297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4373297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4373297 prefixEnd_4373297 := by exact prefixLift 4373297
  have htrace : WordTrace (prefixWord ++ tailWord_4373297) baseStart_4373297 baseEnd_4373297 := by
    simpa [prefixWord, tailWord_4373297, baseEnd_4373297] using wordTrace_append hprefix tailTrace_4373297
  have hstable : (prefixWord ++ tailWord_4373297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4373297).length < 2 ^ (prefixWord ++ tailWord_4373297).sum := by decide
  have hdescent : baseEnd_4373297 < baseStart_4373297 := by decide
  rcases family_descends (prefixWord ++ tailWord_4373297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4373311 : List Nat := [1, 1, 2, 2, 5, 1, 2, 1, 4, 2, 2]
def baseStart_4373311 : Nat := 118140960795 + 4373311 * 2 ^ 59
def prefixEnd_4373311 : Nat := 4983230072969 + 3 ^ 40 * 4373311 * 2
def baseEnd_4373311 : Nat := 2245610594595044134300015

theorem tailTrace_4373311 : CollatzResearch.WordTrace tailWord_4373311 prefixEnd_4373311 2245610594595044134300015 := by
  unfold tailWord_4373311
  simp only [CollatzResearch.WordTrace]
  refine ⟨159507756259248623899999787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106338504172832415933333191 159507756259248623899999787)
  ·
    refine ⟨239261634388872935849999681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159507756259248623899999787 239261634388872935849999681)
    ·
      refine ⟨179446225791654701887499761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 239261634388872935849999681 179446225791654701887499761)
      ·
        refine ⟨134584669343741026415624821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179446225791654701887499761 134584669343741026415624821)
        ·
          refine ⟨12617312750975721226464827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 134584669343741026415624821 12617312750975721226464827)
          ·
            refine ⟨18925969126463581839697241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12617312750975721226464827 18925969126463581839697241)
            ·
              refine ⟨14194476844847686379772931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18925969126463581839697241 14194476844847686379772931)
              ·
                refine ⟨21291715267271529569659397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14194476844847686379772931 21291715267271529569659397)
                ·
                  refine ⟨3992196612613411794311137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21291715267271529569659397 3992196612613411794311137)
                  ·
                    refine ⟨2994147459460058845733353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3992196612613411794311137 2994147459460058845733353)
                    ·
                      refine ⟨2245610594595044134300015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2994147459460058845733353 2245610594595044134300015)
                      ·
                        rfl

theorem cell23_4373311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 4, 2, 2].length) (baseStart_4373311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4373311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4373311 prefixEnd_4373311 := by exact prefixLift 4373311
  have htrace : WordTrace (prefixWord ++ tailWord_4373311) baseStart_4373311 baseEnd_4373311 := by
    simpa [prefixWord, tailWord_4373311, baseEnd_4373311] using wordTrace_append hprefix tailTrace_4373311
  have hstable : (prefixWord ++ tailWord_4373311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4373311).length < 2 ^ (prefixWord ++ tailWord_4373311).sum := by decide
  have hdescent : baseEnd_4373311 < baseStart_4373311 := by decide
  rcases family_descends (prefixWord ++ tailWord_4373311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4373328 : List Nat := [2, 1, 1, 1, 1, 4, 6, 1, 2, 2, 2]
def baseStart_4373328 : Nat := 118140960795 + 4373328 * 2 ^ 59
def prefixEnd_4373328 : Nat := 4983230072969 + 3 ^ 40 * 4373328 * 2
def baseEnd_4373328 : Nat := 2245619323766170567787437

theorem tailTrace_4373328 : CollatzResearch.WordTrace tailWord_4373328 prefixEnd_4373328 2245619323766170567787437 := by
  unfold tailWord_4373328
  simp only [CollatzResearch.WordTrace]
  refine ⟨79754188150093517901684319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106338917533458023868912425 79754188150093517901684319)
  ·
    refine ⟨119631282225140276852526479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79754188150093517901684319 119631282225140276852526479)
    ·
      refine ⟨179446923337710415278789719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119631282225140276852526479 179446923337710415278789719)
      ·
        refine ⟨269170385006565622918184579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179446923337710415278789719 269170385006565622918184579)
        ·
          refine ⟨403755577509848434377276869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 269170385006565622918184579 403755577509848434377276869)
          ·
            refine ⟨75704170783096581445739413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 403755577509848434377276869 75704170783096581445739413)
            ·
              refine ⟨3548633005457652255269035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 75704170783096581445739413 3548633005457652255269035)
              ·
                refine ⟨5322949508186478382903553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3548633005457652255269035 5322949508186478382903553)
                ·
                  refine ⟨3992212131139858787177665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5322949508186478382903553 3992212131139858787177665)
                  ·
                    refine ⟨2994159098354894090383249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3992212131139858787177665 2994159098354894090383249)
                    ·
                      refine ⟨2245619323766170567787437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2994159098354894090383249 2245619323766170567787437)
                      ·
                        rfl

theorem cell23_4373328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 6, 1, 2, 2, 2].length) (baseStart_4373328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4373328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4373328 prefixEnd_4373328 := by exact prefixLift 4373328
  have htrace : WordTrace (prefixWord ++ tailWord_4373328) baseStart_4373328 baseEnd_4373328 := by
    simpa [prefixWord, tailWord_4373328, baseEnd_4373328] using wordTrace_append hprefix tailTrace_4373328
  have hstable : (prefixWord ++ tailWord_4373328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4373328).length < 2 ^ (prefixWord ++ tailWord_4373328).sum := by decide
  have hdescent : baseEnd_4373328 < baseStart_4373328 := by decide
  rcases family_descends (prefixWord ++ tailWord_4373328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4373398 : List Nat := [5, 3, 1, 1, 1, 2, 1, 1, 1, 7]
def baseStart_4373398 : Nat := 118140960795 + 4373398 * 2 ^ 59
def prefixEnd_4373398 : Nat := 4983230072969 + 3 ^ 40 * 4373398 * 2
def baseEnd_4373398 : Nat := 748551755803995097970705

theorem tailTrace_4373398 : CollatzResearch.WordTrace tailWord_4373398 prefixEnd_4373398 748551755803995097970705 := by
  unfold tailWord_4373398
  simp only [CollatzResearch.WordTrace]
  refine ⟨9969433088120839859901053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 106340619606622291838944565 9969433088120839859901053)
  ·
    refine ⟨3738537408045314947462895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9969433088120839859901053 3738537408045314947462895)
    ·
      refine ⟨5607806112067972421194343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3738537408045314947462895 5607806112067972421194343)
      ·
        refine ⟨8411709168101958631791515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5607806112067972421194343 8411709168101958631791515)
        ·
          refine ⟨12617563752152937947687273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8411709168101958631791515 12617563752152937947687273)
          ·
            refine ⟨9463172814114703460765455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12617563752152937947687273 9463172814114703460765455)
            ·
              refine ⟨14194759221172055191148183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9463172814114703460765455 14194759221172055191148183)
              ·
                refine ⟨21292138831758082786722275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14194759221172055191148183 21292138831758082786722275)
                ·
                  refine ⟨31938208247637124180083413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21292138831758082786722275 31938208247637124180083413)
                  ·
                    refine ⟨748551755803995097970705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31938208247637124180083413 748551755803995097970705)
                    ·
                      rfl

theorem cell23_4373398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_4373398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4373398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4373398 prefixEnd_4373398 := by exact prefixLift 4373398
  have htrace : WordTrace (prefixWord ++ tailWord_4373398) baseStart_4373398 baseEnd_4373398 := by
    simpa [prefixWord, tailWord_4373398, baseEnd_4373398] using wordTrace_append hprefix tailTrace_4373398
  have hstable : (prefixWord ++ tailWord_4373398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4373398).length < 2 ^ (prefixWord ++ tailWord_4373398).sum := by decide
  have hdescent : baseEnd_4373398 < baseStart_4373398 := by decide
  rcases family_descends (prefixWord ++ tailWord_4373398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4373411 : List Nat := [1, 1, 1, 4, 1, 2, 3, 5, 1, 4]
def baseStart_4373411 : Nat := 118140960795 + 4373411 * 2 ^ 59
def prefixEnd_4373411 : Nat := 4983230072969 + 3 ^ 40 * 4373411 * 2
def baseEnd_4373411 : Nat := 748553980886831247683185

theorem tailTrace_4373411 : CollatzResearch.WordTrace tailWord_4373411 prefixEnd_4373411 748553980886831247683185 := by
  unfold tailWord_4373411
  simp only [CollatzResearch.WordTrace]
  refine ⟨159511403558886340978640087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106340935705924227319093391 159511403558886340978640087)
  ·
    refine ⟨239267105338329511467960131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159511403558886340978640087 239267105338329511467960131)
    ·
      refine ⟨358900658007494267201940197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239267105338329511467960131 358900658007494267201940197)
      ·
        refine ⟨67293873376405175100363787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 358900658007494267201940197 67293873376405175100363787)
        ·
          refine ⟨100940810064607762650545681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67293873376405175100363787 100940810064607762650545681)
          ·
            refine ⟨75705607548455821987909261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100940810064607762650545681 75705607548455821987909261)
            ·
              refine ⟨28389602830670933245465973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75705607548455821987909261 28389602830670933245465973)
              ·
                refine ⟨2661525265375399991762435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28389602830670933245465973 2661525265375399991762435)
                ·
                  refine ⟨3992287898063099987643653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2661525265375399991762435 3992287898063099987643653)
                  ·
                    refine ⟨748553980886831247683185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3992287898063099987643653 748553980886831247683185)
                    ·
                      rfl

theorem cell23_4373411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 5, 1, 4].length) (baseStart_4373411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4373411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4373411 prefixEnd_4373411 := by exact prefixLift 4373411
  have htrace : WordTrace (prefixWord ++ tailWord_4373411) baseStart_4373411 baseEnd_4373411 := by
    simpa [prefixWord, tailWord_4373411, baseEnd_4373411] using wordTrace_append hprefix tailTrace_4373411
  have hstable : (prefixWord ++ tailWord_4373411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4373411).length < 2 ^ (prefixWord ++ tailWord_4373411).sum := by decide
  have hdescent : baseEnd_4373411 < baseStart_4373411 := by decide
  rcases family_descends (prefixWord ++ tailWord_4373411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4373428 : List Nat := [2, 5, 2, 1, 1, 1, 1, 3, 3, 4]
def baseStart_4373428 : Nat := 118140960795 + 4373428 * 2 ^ 59
def prefixEnd_4373428 : Nat := 4983230072969 + 3 ^ 40 * 4373428 * 2
def baseEnd_4373428 : Nat := 748556890610540058845659

theorem tailTrace_4373428 : CollatzResearch.WordTrace tailWord_4373428 prefixEnd_4373428 748556890610540058845659 := by
  unfold tailWord_4373428
  simp only [CollatzResearch.WordTrace]
  refine ⟨79756011799912376441004469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106341349066549835254672625 79756011799912376441004469)
  ·
    refine ⟨7477126106241785291344169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 79756011799912376441004469 7477126106241785291344169)
    ·
      refine ⟨5607844579681338968508127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7477126106241785291344169 5607844579681338968508127)
      ·
        refine ⟨8411766869522008452762191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5607844579681338968508127 8411766869522008452762191)
        ·
          refine ⟨12617650304283012679143287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8411766869522008452762191 12617650304283012679143287)
          ·
            refine ⟨18926475456424519018714931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12617650304283012679143287 18926475456424519018714931)
            ·
              refine ⟨28389713184636778528072397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18926475456424519018714931 28389713184636778528072397)
              ·
                refine ⟨10646142444238791948027149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28389713184636778528072397 10646142444238791948027149)
                ·
                  refine ⟨3992303416589546980510181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10646142444238791948027149 3992303416589546980510181)
                  ·
                    refine ⟨748556890610540058845659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3992303416589546980510181 748556890610540058845659)
                    ·
                      rfl

theorem cell23_4373428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_4373428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4373428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4373428 prefixEnd_4373428 := by exact prefixLift 4373428
  have htrace : WordTrace (prefixWord ++ tailWord_4373428) baseStart_4373428 baseEnd_4373428 := by
    simpa [prefixWord, tailWord_4373428, baseEnd_4373428] using wordTrace_append hprefix tailTrace_4373428
  have hstable : (prefixWord ++ tailWord_4373428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4373428).length < 2 ^ (prefixWord ++ tailWord_4373428).sum := by decide
  have hdescent : baseEnd_4373428 < baseStart_4373428 := by decide
  rcases family_descends (prefixWord ++ tailWord_4373428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4373447 : List Nat := [1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 7]
def baseStart_4373447 : Nat := 118140960795 + 4373447 * 2 ^ 59
def prefixEnd_4373447 : Nat := 4983230072969 + 3 ^ 40 * 4373447 * 2
def baseEnd_4373447 : Nat := 2245680427964055602199389

theorem tailTrace_4373447 : CollatzResearch.WordTrace tailWord_4373447 prefixEnd_4373447 2245680427964055602199389 := by
  unfold tailWord_4373447
  simp only [CollatzResearch.WordTrace]
  refine ⟨159512716586755919126950595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106341811057837279417967063 159512716586755919126950595)
  ·
    refine ⟨239269074880133878690425893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159512716586755919126950595 239269074880133878690425893)
    ·
      refine ⟨44862951540025102254454855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 239269074880133878690425893 44862951540025102254454855)
      ·
        refine ⟨67294427310037653381682283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44862951540025102254454855 67294427310037653381682283)
        ·
          refine ⟨100941640965056480072523425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67294427310037653381682283 100941640965056480072523425)
          ·
            refine ⟨75706230723792360054392569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100941640965056480072523425 75706230723792360054392569)
            ·
              refine ⟨56779673042844270040794427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75706230723792360054392569 56779673042844270040794427)
              ·
                refine ⟨85169509564266405061191641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56779673042844270040794427 85169509564266405061191641)
                ·
                  refine ⟨63877132173199803795893731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85169509564266405061191641 63877132173199803795893731)
                  ·
                    refine ⟨95815698259799705693840597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 63877132173199803795893731 95815698259799705693840597)
                    ·
                      refine ⟨2245680427964055602199389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 95815698259799705693840597 2245680427964055602199389)
                      ·
                        rfl

theorem cell23_4373447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_4373447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4373447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4373447 prefixEnd_4373447 := by exact prefixLift 4373447
  have htrace : WordTrace (prefixWord ++ tailWord_4373447) baseStart_4373447 baseEnd_4373447 := by
    simpa [prefixWord, tailWord_4373447, baseEnd_4373447] using wordTrace_append hprefix tailTrace_4373447
  have hstable : (prefixWord ++ tailWord_4373447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4373447).length < 2 ^ (prefixWord ++ tailWord_4373447).sum := by decide
  have hdescent : baseEnd_4373447 < baseStart_4373447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4373447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4373451 : List Nat := [1, 1, 1, 1, 3, 5, 2, 2, 3, 1, 3]
def baseStart_4373451 : Nat := 118140960795 + 4373451 * 2 ^ 59
def prefixEnd_4373451 : Nat := 4983230072969 + 3 ^ 40 * 4373451 * 2
def baseEnd_4373451 : Nat := 2245682481886673586549371

theorem tailTrace_4373451 : CollatzResearch.WordTrace tailWord_4373451 prefixEnd_4373451 2245682481886673586549371 := by
  unfold tailWord_4373451
  simp only [CollatzResearch.WordTrace]
  refine ⟨159512862478741427810096207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106341908319160951873397471 159512862478741427810096207)
  ·
    refine ⟨239269293718112141715144311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159512862478741427810096207 239269293718112141715144311)
    ·
      refine ⟨358903940577168212572716467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239269293718112141715144311 358903940577168212572716467)
      ·
        refine ⟨538355910865752318859074701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 358903940577168212572716467 538355910865752318859074701)
        ·
          refine ⟨201883466574657119572153013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 538355910865752318859074701 201883466574657119572153013)
          ·
            refine ⟨18926574991374104959889345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 201883466574657119572153013 18926574991374104959889345)
            ·
              refine ⟨14194931243530578719917009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18926574991374104959889345 14194931243530578719917009)
              ·
                refine ⟨10646198432647934039937757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14194931243530578719917009 10646198432647934039937757)
                ·
                  refine ⟨3992324412242975264976659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10646198432647934039937757 3992324412242975264976659)
                  ·
                    refine ⟨5988486618364462897464989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3992324412242975264976659 5988486618364462897464989)
                    ·
                      refine ⟨2245682481886673586549371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5988486618364462897464989 2245682481886673586549371)
                      ·
                        rfl

theorem cell23_4373451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 2, 3, 1, 3].length) (baseStart_4373451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4373451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4373451 prefixEnd_4373451 := by exact prefixLift 4373451
  have htrace : WordTrace (prefixWord ++ tailWord_4373451) baseStart_4373451 baseEnd_4373451 := by
    simpa [prefixWord, tailWord_4373451, baseEnd_4373451] using wordTrace_append hprefix tailTrace_4373451
  have hstable : (prefixWord ++ tailWord_4373451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4373451).length < 2 ^ (prefixWord ++ tailWord_4373451).sum := by decide
  have hdescent : baseEnd_4373451 < baseStart_4373451 := by decide
  rcases family_descends (prefixWord ++ tailWord_4373451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4373462 : List Nat := [5, 2, 1, 1, 2, 3, 1, 3, 1, 4]
def baseStart_4373462 : Nat := 118140960795 + 4373462 * 2 ^ 59
def prefixEnd_4373462 : Nat := 4983230072969 + 3 ^ 40 * 4373462 * 2
def baseEnd_4373462 : Nat := 748562710057957681170607

theorem tailTrace_4373462 : CollatzResearch.WordTrace tailWord_4373462 prefixEnd_4373462 748562710057957681170607 := by
  unfold tailWord_4373462
  simp only [CollatzResearch.WordTrace]
  refine ⟨9969578980106348543046665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 106342175787801051125831093 9969578980106348543046665)
  ·
    refine ⟨7477184235079761407284999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9969578980106348543046665 7477184235079761407284999)
    ·
      refine ⟨11215776352619642110927499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7477184235079761407284999 11215776352619642110927499)
      ·
        refine ⟨16823664528929463166391249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11215776352619642110927499 16823664528929463166391249)
        ·
          refine ⟨12617748396697097374793437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16823664528929463166391249 12617748396697097374793437)
          ·
            refine ⟨4731655648761411515547539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12617748396697097374793437 4731655648761411515547539)
            ·
              refine ⟨7097483473142117273321309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4731655648761411515547539 7097483473142117273321309)
              ·
                refine ⟨2661556302428293977495491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7097483473142117273321309 2661556302428293977495491)
                ·
                  refine ⟨3992334453642440966243237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2661556302428293977495491 3992334453642440966243237)
                  ·
                    refine ⟨748562710057957681170607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3992334453642440966243237 748562710057957681170607)
                    ·
                      rfl

theorem cell23_4373462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_4373462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4373462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4373462 prefixEnd_4373462 := by exact prefixLift 4373462
  have htrace : WordTrace (prefixWord ++ tailWord_4373462) baseStart_4373462 baseEnd_4373462 := by
    simpa [prefixWord, tailWord_4373462, baseEnd_4373462] using wordTrace_append hprefix tailTrace_4373462
  have hstable : (prefixWord ++ tailWord_4373462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4373462).length < 2 ^ (prefixWord ++ tailWord_4373462).sum := by decide
  have hdescent : baseEnd_4373462 < baseStart_4373462 := by decide
  rcases family_descends (prefixWord ++ tailWord_4373462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4373492 : List Nat := [2, 6, 2, 1, 1, 1, 1, 3, 6]
def baseStart_4373492 : Nat := 118140960795 + 4373492 * 2 ^ 59
def prefixEnd_4373492 : Nat := 4983230072969 + 3 ^ 40 * 4373492 * 2
def baseEnd_4373492 : Nat := 249522614954834214015187

theorem tailTrace_4373492 : CollatzResearch.WordTrace tailWord_4373492 prefixEnd_4373492 249522614954834214015187 := by
  unfold tailWord_4373492
  simp only [CollatzResearch.WordTrace]
  refine ⟨79757178935796445906169365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106342905247728594541559153 79757178935796445906169365)
  ·
    refine ⟨3738617762615458401851689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 79757178935796445906169365 3738617762615458401851689)
    ·
      refine ⟨2803963321961593801388767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3738617762615458401851689 2803963321961593801388767)
      ·
        refine ⟨4205944982942390702083151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2803963321961593801388767 4205944982942390702083151)
        ·
          refine ⟨6308917474413586053124727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4205944982942390702083151 6308917474413586053124727)
          ·
            refine ⟨9463376211620379079687091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6308917474413586053124727 9463376211620379079687091)
            ·
              refine ⟨14195064317430568619530637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9463376211620379079687091 14195064317430568619530637)
              ·
                refine ⟨5323149119036463232323989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14195064317430568619530637 5323149119036463232323989)
                ·
                  refine ⟨249522614954834214015187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5323149119036463232323989 249522614954834214015187)
                  ·
                    rfl

theorem cell23_4373492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_4373492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4373492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4373492 prefixEnd_4373492 := by exact prefixLift 4373492
  have htrace : WordTrace (prefixWord ++ tailWord_4373492) baseStart_4373492 baseEnd_4373492 := by
    simpa [prefixWord, tailWord_4373492, baseEnd_4373492] using wordTrace_append hprefix tailTrace_4373492
  have hstable : (prefixWord ++ tailWord_4373492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4373492).length < 2 ^ (prefixWord ++ tailWord_4373492).sum := by decide
  have hdescent : baseEnd_4373492 < baseStart_4373492 := by decide
  rcases family_descends (prefixWord ++ tailWord_4373492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4373511 : List Nat := [1, 1, 4, 3, 1, 1, 3, 1, 3, 2, 3]
def baseStart_4373511 : Nat := 118140960795 + 4373511 * 2 ^ 59
def prefixEnd_4373511 : Nat := 4983230072969 + 3 ^ 40 * 4373511 * 2
def baseEnd_4373511 : Nat := 2245713290725943351799095

theorem tailTrace_4373511 : CollatzResearch.WordTrace tailWord_4373511 prefixEnd_4373511 2245713290725943351799095 := by
  unfold tailWord_4373511
  simp only [CollatzResearch.WordTrace]
  refine ⟨159515050858524058057280387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106343367239016038704853591 159515050858524058057280387)
  ·
    refine ⟨239272576287786087085920581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159515050858524058057280387 239272576287786087085920581)
    ·
      refine ⟨44863608053959891328610109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 239272576287786087085920581 44863608053959891328610109)
      ·
        refine ⟨16823853020234959248228791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44863608053959891328610109 16823853020234959248228791)
        ·
          refine ⟨25235779530352438872343187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16823853020234959248228791 25235779530352438872343187)
          ·
            refine ⟨37853669295528658308514781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25235779530352438872343187 37853669295528658308514781)
            ·
              refine ⟨14195125985823246865693043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37853669295528658308514781 14195125985823246865693043)
              ·
                refine ⟨21292688978734870298539565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14195125985823246865693043 21292688978734870298539565)
                ·
                  refine ⟨7984758367025576361952337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21292688978734870298539565 7984758367025576361952337)
                  ·
                    refine ⟨5988568775269182271464253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7984758367025576361952337 5988568775269182271464253)
                    ·
                      refine ⟨2245713290725943351799095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5988568775269182271464253 2245713290725943351799095)
                      ·
                        rfl

theorem cell23_4373511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_4373511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4373511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4373511 prefixEnd_4373511 := by exact prefixLift 4373511
  have htrace : WordTrace (prefixWord ++ tailWord_4373511) baseStart_4373511 baseEnd_4373511 := by
    simpa [prefixWord, tailWord_4373511, baseEnd_4373511] using wordTrace_append hprefix tailTrace_4373511
  have hstable : (prefixWord ++ tailWord_4373511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4373511).length < 2 ^ (prefixWord ++ tailWord_4373511).sum := by decide
  have hdescent : baseEnd_4373511 < baseStart_4373511 := by decide
  rcases family_descends (prefixWord ++ tailWord_4373511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4373514 : List Nat := [3, 1, 2, 2, 3, 1, 2, 9]
def baseStart_4373514 : Nat := 118140960795 + 4373514 * 2 ^ 59
def prefixEnd_4373514 : Nat := 4983230072969 + 3 ^ 40 * 4373514 * 2
def baseEnd_4373514 : Nat := 83174623376589142224503

theorem tailTrace_4373514 : CollatzResearch.WordTrace tailWord_4373514 prefixEnd_4373514 83174623376589142224503 := by
  unfold tailWord_4373514
  simp only [CollatzResearch.WordTrace]
  refine ⟨39878790069378297392409899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106343440185008793046426397 39878790069378297392409899)
  ·
    refine ⟨59818185104067446088614849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39878790069378297392409899 59818185104067446088614849)
    ·
      refine ⟨44863638828050584566461137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59818185104067446088614849 44863638828050584566461137)
      ·
        refine ⟨33647729121037938424845853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44863638828050584566461137 33647729121037938424845853)
        ·
          refine ⟨12617898420389226909317195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33647729121037938424845853 12617898420389226909317195)
          ·
            refine ⟨18926847630583840363975793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12617898420389226909317195 18926847630583840363975793)
            ·
              refine ⟨14195135722937880272981845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18926847630583840363975793 14195135722937880272981845)
              ·
                refine ⟨83174623376589142224503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14195135722937880272981845 83174623376589142224503)
                ·
                  rfl

theorem cell23_4373514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 9].length) (baseStart_4373514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4373514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4373514 prefixEnd_4373514 := by exact prefixLift 4373514
  have htrace : WordTrace (prefixWord ++ tailWord_4373514) baseStart_4373514 baseEnd_4373514 := by
    simpa [prefixWord, tailWord_4373514, baseEnd_4373514] using wordTrace_append hprefix tailTrace_4373514
  have hstable : (prefixWord ++ tailWord_4373514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4373514).length < 2 ^ (prefixWord ++ tailWord_4373514).sum := by decide
  have hdescent : baseEnd_4373514 < baseStart_4373514 := by decide
  rcases family_descends (prefixWord ++ tailWord_4373514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4373536 : List Nat := [2, 1, 1, 7, 2, 1, 2, 2, 1, 1, 3]
def baseStart_4373536 : Nat := 118140960795 + 4373536 * 2 ^ 59
def prefixEnd_4373536 : Nat := 4983230072969 + 3 ^ 40 * 4373536 * 2
def baseEnd_4373536 : Nat := 2245726127742305753986481

theorem tailTrace_4373536 : CollatzResearch.WordTrace tailWord_4373536 prefixEnd_4373536 2245726127742305753986481 := by
  unfold tailWord_4373536
  simp only [CollatzResearch.WordTrace]
  refine ⟨79757981341716743663470231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106343975122288991551293641 79757981341716743663470231)
  ·
    refine ⟨119636972012575115495205347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79757981341716743663470231 119636972012575115495205347)
    ·
      refine ⟨179455458018862673242808021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119636972012575115495205347 179455458018862673242808021)
      ·
        refine ⟨4205987297317093904128313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 179455458018862673242808021 4205987297317093904128313)
        ·
          refine ⟨3154490472987820428096235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4205987297317093904128313 3154490472987820428096235)
          ·
            refine ⟨4731735709481730642144353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3154490472987820428096235 4731735709481730642144353)
            ·
              refine ⟨3548801782111297981608265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4731735709481730642144353 3548801782111297981608265)
              ·
                refine ⟨2661601336583473486206199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3548801782111297981608265 2661601336583473486206199)
                ·
                  refine ⟨3992402004875210229309299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2661601336583473486206199 3992402004875210229309299)
                  ·
                    refine ⟨5988603007312815343963949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3992402004875210229309299 5988603007312815343963949)
                    ·
                      refine ⟨2245726127742305753986481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5988603007312815343963949 2245726127742305753986481)
                      ·
                        rfl

theorem cell23_4373536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_4373536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4373536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4373536 prefixEnd_4373536 := by exact prefixLift 4373536
  have htrace : WordTrace (prefixWord ++ tailWord_4373536) baseStart_4373536 baseEnd_4373536 := by
    simpa [prefixWord, tailWord_4373536, baseEnd_4373536] using wordTrace_append hprefix tailTrace_4373536
  have hstable : (prefixWord ++ tailWord_4373536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4373536).length < 2 ^ (prefixWord ++ tailWord_4373536).sum := by decide
  have hdescent : baseEnd_4373536 < baseStart_4373536 := by decide
  rcases family_descends (prefixWord ++ tailWord_4373536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4373558 : List Nat := [5, 1, 2, 1, 1, 2, 1, 3, 1, 3, 3]
def baseStart_4373558 : Nat := 118140960795 + 4373558 * 2 ^ 59
def prefixEnd_4373558 : Nat := 4983230072969 + 3 ^ 40 * 4373558 * 2
def baseEnd_4373558 : Nat := 2245737424316704667911379

theorem tailTrace_4373558 : CollatzResearch.WordTrace tailWord_4373558 prefixEnd_4373558 2245737424316704667911379 := by
  unfold tailWord_4373558
  simp only [CollatzResearch.WordTrace]
  refine ⟨9969797818084611567765083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 106344510059569190056160885 9969797818084611567765083)
  ·
    refine ⟨14954696727126917351647625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9969797818084611567765083 14954696727126917351647625)
    ·
      refine ⟨11216022545345188013735719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14954696727126917351647625 11216022545345188013735719)
      ·
        refine ⟨16824033818017782020603579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11216022545345188013735719 16824033818017782020603579)
        ·
          refine ⟨25236050727026673030905369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16824033818017782020603579 25236050727026673030905369)
          ·
            refine ⟨18927038045270004773179027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25236050727026673030905369 18927038045270004773179027)
            ·
              refine ⟨28390557067905007159768541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18927038045270004773179027 28390557067905007159768541)
              ·
                refine ⟨10646458900464377684913203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28390557067905007159768541 10646458900464377684913203)
                ·
                  refine ⟨15969688350696566527369805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10646458900464377684913203 15969688350696566527369805)
                  ·
                    refine ⟨5988633131511212447763677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15969688350696566527369805 5988633131511212447763677)
                    ·
                      refine ⟨2245737424316704667911379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5988633131511212447763677 2245737424316704667911379)
                      ·
                        rfl

theorem cell23_4373558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_4373558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4373558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4373558 prefixEnd_4373558 := by exact prefixLift 4373558
  have htrace : WordTrace (prefixWord ++ tailWord_4373558) baseStart_4373558 baseEnd_4373558 := by
    simpa [prefixWord, tailWord_4373558, baseEnd_4373558] using wordTrace_append hprefix tailTrace_4373558
  have hstable : (prefixWord ++ tailWord_4373558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4373558).length < 2 ^ (prefixWord ++ tailWord_4373558).sum := by decide
  have hdescent : baseEnd_4373558 < baseStart_4373558 := by decide
  rcases family_descends (prefixWord ++ tailWord_4373558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4373568 : List Nat := [2, 1, 1, 2, 2, 3, 2, 4, 1, 3, 2]
def baseStart_4373568 : Nat := 118140960795 + 4373568 * 2 ^ 59
def prefixEnd_4373568 : Nat := 4983230072969 + 3 ^ 40 * 4373568 * 2
def baseEnd_4373568 : Nat := 2245742559123249628786333

theorem tailTrace_4373568 : CollatzResearch.WordTrace tailWord_4373568 prefixEnd_4373568 2245742559123249628786333 := by
  unfold tailWord_4373568
  simp only [CollatzResearch.WordTrace]
  refine ⟨79758564909658778396052679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106344753212878371194736905 79758564909658778396052679)
  ·
    refine ⟨119637847364488167594079019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79758564909658778396052679 119637847364488167594079019)
    ·
      refine ⟨179456771046732251391118529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119637847364488167594079019 179456771046732251391118529)
      ·
        refine ⟨134592578285049188543338897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179456771046732251391118529 134592578285049188543338897)
        ·
          refine ⟨100944433713786891407504173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134592578285049188543338897 100944433713786891407504173)
          ·
            refine ⟨37854162642670084277814065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100944433713786891407504173 37854162642670084277814065)
            ·
              refine ⟨28390621982002563208360549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37854162642670084277814065 28390621982002563208360549)
              ·
                refine ⟨5323241621625480601567603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28390621982002563208360549 5323241621625480601567603)
                ·
                  refine ⟨7984862432438220902351405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5323241621625480601567603 7984862432438220902351405)
                  ·
                    refine ⟨2994323412164332838381777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7984862432438220902351405 2994323412164332838381777)
                    ·
                      refine ⟨2245742559123249628786333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2994323412164332838381777 2245742559123249628786333)
                      ·
                        rfl

theorem cell23_4373568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 4, 1, 3, 2].length) (baseStart_4373568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4373568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4373568 prefixEnd_4373568 := by exact prefixLift 4373568
  have htrace : WordTrace (prefixWord ++ tailWord_4373568) baseStart_4373568 baseEnd_4373568 := by
    simpa [prefixWord, tailWord_4373568, baseEnd_4373568] using wordTrace_append hprefix tailTrace_4373568
  have hstable : (prefixWord ++ tailWord_4373568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4373568).length < 2 ^ (prefixWord ++ tailWord_4373568).sum := by decide
  have hdescent : baseEnd_4373568 < baseStart_4373568 := by decide
  rcases family_descends (prefixWord ++ tailWord_4373568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4373584 : List Nat := [2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 5]
def baseStart_4373584 : Nat := 118140960795 + 4373584 * 2 ^ 59
def prefixEnd_4373584 : Nat := 4983230072969 + 3 ^ 40 * 4373584 * 2
def baseEnd_4373584 : Nat := 2245750774813721566186259

theorem tailTrace_4373584 : CollatzResearch.WordTrace tailWord_4373584 prefixEnd_4373584 2245750774813721566186259 := by
  unfold tailWord_4373584
  simp only [CollatzResearch.WordTrace]
  refine ⟨79758856693629795762343903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106345142258173061016458537 79758856693629795762343903)
  ·
    refine ⟨119638285040444693643515855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79758856693629795762343903 119638285040444693643515855)
    ·
      refine ⟨179457427560667040465273783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119638285040444693643515855 179457427560667040465273783)
      ·
        refine ⟨269186141341000560697910675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179457427560667040465273783 269186141341000560697910675)
        ·
          refine ⟨403779212011500841046866013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 269186141341000560697910675 403779212011500841046866013)
          ·
            refine ⟨151417204504312815392574755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 403779212011500841046866013 151417204504312815392574755)
            ·
              refine ⟨227125806756469223088862133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151417204504312815392574755 227125806756469223088862133)
              ·
                refine ⟨21293044383418989664580825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 227125806756469223088862133 21293044383418989664580825)
                ·
                  refine ⟨15969783287564242248435619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21293044383418989664580825 15969783287564242248435619)
                  ·
                    refine ⟨23954674931346363372653429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15969783287564242248435619 23954674931346363372653429)
                    ·
                      refine ⟨2245750774813721566186259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23954674931346363372653429 2245750774813721566186259)
                      ·
                        rfl

theorem cell23_4373584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 5].length) (baseStart_4373584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4373584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4373584 prefixEnd_4373584 := by exact prefixLift 4373584
  have htrace : WordTrace (prefixWord ++ tailWord_4373584) baseStart_4373584 baseEnd_4373584 := by
    simpa [prefixWord, tailWord_4373584, baseEnd_4373584] using wordTrace_append hprefix tailTrace_4373584
  have hstable : (prefixWord ++ tailWord_4373584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4373584).length < 2 ^ (prefixWord ++ tailWord_4373584).sum := by decide
  have hdescent : baseEnd_4373584 < baseStart_4373584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4373584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4373585 : List Nat := [1, 2, 2, 1, 3, 1, 6, 1, 1, 3, 2]
def baseStart_4373585 : Nat := 118140960795 + 4373585 * 2 ^ 59
def prefixEnd_4373585 : Nat := 4983230072969 + 3 ^ 40 * 4373585 * 2
def baseEnd_4373585 : Nat := 2245751288294376062273755

theorem tailTrace_4373585 : CollatzResearch.WordTrace tailWord_4373585 prefixEnd_4373585 2245751288294376062273755 := by
  unfold tailWord_4373585
  simp only [CollatzResearch.WordTrace]
  refine ⟨159517749860255968695474209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106345166573503979130316139 159517749860255968695474209)
  ·
    refine ⟨119638312395191976521605657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159517749860255968695474209 119638312395191976521605657)
    ·
      refine ⟨89728734296393982391204243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119638312395191976521605657 89728734296393982391204243)
      ·
        refine ⟨134593101444590973586806365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89728734296393982391204243 134593101444590973586806365)
        ·
          refine ⟨50472413041721615095052387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134593101444590973586806365 50472413041721615095052387)
          ·
            refine ⟨75708619562582422642578581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50472413041721615095052387 75708619562582422642578581)
            ·
              refine ⟨3548841541996051061370871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 75708619562582422642578581 3548841541996051061370871)
              ·
                refine ⟨5323262312994076592056307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3548841541996051061370871 5323262312994076592056307)
                ·
                  refine ⟨7984893469491114888084461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5323262312994076592056307 7984893469491114888084461)
                  ·
                    refine ⟨2994335051059168083031673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7984893469491114888084461 2994335051059168083031673)
                    ·
                      refine ⟨2245751288294376062273755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2994335051059168083031673 2245751288294376062273755)
                      ·
                        rfl

theorem cell23_4373585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 6, 1, 1, 3, 2].length) (baseStart_4373585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4373585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4373585 prefixEnd_4373585 := by exact prefixLift 4373585
  have htrace : WordTrace (prefixWord ++ tailWord_4373585) baseStart_4373585 baseEnd_4373585 := by
    simpa [prefixWord, tailWord_4373585, baseEnd_4373585] using wordTrace_append hprefix tailTrace_4373585
  have hstable : (prefixWord ++ tailWord_4373585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4373585).length < 2 ^ (prefixWord ++ tailWord_4373585).sum := by decide
  have hdescent : baseEnd_4373585 < baseStart_4373585 := by decide
  rcases family_descends (prefixWord ++ tailWord_4373585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4373644 : List Nat := [2, 2, 1, 2, 1, 1, 1, 2, 3, 1, 7]
def baseStart_4373644 : Nat := 118140960795 + 4373644 * 2 ^ 59
def prefixEnd_4373644 : Nat := 4983230072969 + 3 ^ 40 * 4373644 * 2
def baseEnd_4373644 : Nat := 2245781583652991331435983

theorem tailTrace_4373644 : CollatzResearch.WordTrace tailWord_4373644 prefixEnd_4373644 2245781583652991331435983 := by
  unfold tailWord_4373644
  simp only [CollatzResearch.WordTrace]
  refine ⟨79759950883521110885935993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106346601178028147847914657 79759950883521110885935993)
  ·
    refine ⟨59819963162640833164451995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79759950883521110885935993 59819963162640833164451995)
    ·
      refine ⟨89729944743961249746677993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59819963162640833164451995 89729944743961249746677993)
      ·
        refine ⟨67297458557970937310008495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89729944743961249746677993 67297458557970937310008495)
        ·
          refine ⟨100946187836956405965012743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67297458557970937310008495 100946187836956405965012743)
          ·
            refine ⟨151419281755434608947519115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100946187836956405965012743 151419281755434608947519115)
            ·
              refine ⟨227128922633151913421278673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151419281755434608947519115 227128922633151913421278673)
              ·
                refine ⟨170346691974863935065959005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 227128922633151913421278673 170346691974863935065959005)
                ·
                  refine ⟨63880009490573975649734627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 170346691974863935065959005 63880009490573975649734627)
                  ·
                    refine ⟨95820014235860963474601941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 63880009490573975649734627 95820014235860963474601941)
                    ·
                      refine ⟨2245781583652991331435983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 95820014235860963474601941 2245781583652991331435983)
                      ·
                        rfl

theorem cell23_4373644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_4373644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4373644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4373644 prefixEnd_4373644 := by exact prefixLift 4373644
  have htrace : WordTrace (prefixWord ++ tailWord_4373644) baseStart_4373644 baseEnd_4373644 := by
    simpa [prefixWord, tailWord_4373644, baseEnd_4373644] using wordTrace_append hprefix tailTrace_4373644
  have hstable : (prefixWord ++ tailWord_4373644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4373644).length < 2 ^ (prefixWord ++ tailWord_4373644).sum := by decide
  have hdescent : baseEnd_4373644 < baseStart_4373644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4373644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4373655 : List Nat := [1, 1, 3, 3, 3, 2, 3, 2, 5]
def baseStart_4373655 : Nat := 118140960795 + 4373655 * 2 ^ 59
def prefixEnd_4373655 : Nat := 4983230072969 + 3 ^ 40 * 4373655 * 2
def baseEnd_4373655 : Nat := 249531914660021198710937

theorem tailTrace_4373655 : CollatzResearch.WordTrace tailWord_4373655 prefixEnd_4373655 249531914660021198710937 := by
  unfold tailWord_4373655
  simp only [CollatzResearch.WordTrace]
  refine ⟨159520302970002370650522419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106346868646668247100348279 159520302970002370650522419)
  ·
    refine ⟨239280454455003555975783629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159520302970002370650522419 239280454455003555975783629)
    ·
      refine ⟨89730170420626333490918861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 239280454455003555975783629 89730170420626333490918861)
      ·
        refine ⟨33648813907734875059094573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89730170420626333490918861 33648813907734875059094573)
        ·
          refine ⟨12618305215400578147160465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33648813907734875059094573 12618305215400578147160465)
          ·
            refine ⟨9463728911550433610370349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12618305215400578147160465 9463728911550433610370349)
            ·
              refine ⟨3548898341831412603888881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9463728911550433610370349 3548898341831412603888881)
              ·
                refine ⟨2661673756373559452916661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3548898341831412603888881 2661673756373559452916661)
                ·
                  refine ⟨249531914660021198710937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2661673756373559452916661 249531914660021198710937)
                  ·
                    rfl

theorem cell23_4373655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 3, 2, 5].length) (baseStart_4373655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4373655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4373655 prefixEnd_4373655 := by exact prefixLift 4373655
  have htrace : WordTrace (prefixWord ++ tailWord_4373655) baseStart_4373655 baseEnd_4373655 := by
    simpa [prefixWord, tailWord_4373655, baseEnd_4373655] using wordTrace_append hprefix tailTrace_4373655
  have hstable : (prefixWord ++ tailWord_4373655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4373655).length < 2 ^ (prefixWord ++ tailWord_4373655).sum := by decide
  have hdescent : baseEnd_4373655 < baseStart_4373655 := by decide
  rcases family_descends (prefixWord ++ tailWord_4373655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4373661 : List Nat := [1, 4, 2, 1, 1, 2, 3, 1, 1, 2, 5]
def baseStart_4373661 : Nat := 118140960795 + 4373661 * 2 ^ 59
def prefixEnd_4373661 : Nat := 4983230072969 + 3 ^ 40 * 4373661 * 2
def baseEnd_4373661 : Nat := 2245790312824117764923405

theorem tailTrace_4373661 : CollatzResearch.WordTrace tailWord_4373661 prefixEnd_4373661 2245790312824117764923405 := by
  unfold tailWord_4373661
  simp only [CollatzResearch.WordTrace]
  refine ⟨159520521807980633675240837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106347014538653755783493891 159520521807980633675240837)
  ·
    refine ⟨29910097838996368814107657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 159520521807980633675240837 29910097838996368814107657)
    ·
      refine ⟨22432573379247276610580743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29910097838996368814107657 22432573379247276610580743)
      ·
        refine ⟨33648860068870914915871115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22432573379247276610580743 33648860068870914915871115)
        ·
          refine ⟨50473290103306372373806673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33648860068870914915871115 50473290103306372373806673)
          ·
            refine ⟨37854967577479779280355005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50473290103306372373806673 37854967577479779280355005)
            ·
              refine ⟨14195612841554917230133127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37854967577479779280355005 14195612841554917230133127)
              ·
                refine ⟨21293419262332375845199691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14195612841554917230133127 21293419262332375845199691)
                ·
                  refine ⟨31940128893498563767799537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21293419262332375845199691 31940128893498563767799537)
                  ·
                    refine ⟨23955096670123922825849653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31940128893498563767799537 23955096670123922825849653)
                    ·
                      refine ⟨2245790312824117764923405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23955096670123922825849653 2245790312824117764923405)
                      ·
                        rfl

theorem cell23_4373661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_4373661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4373661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4373661 prefixEnd_4373661 := by exact prefixLift 4373661
  have htrace : WordTrace (prefixWord ++ tailWord_4373661) baseStart_4373661 baseEnd_4373661 := by
    simpa [prefixWord, tailWord_4373661, baseEnd_4373661] using wordTrace_append hprefix tailTrace_4373661
  have hstable : (prefixWord ++ tailWord_4373661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4373661).length < 2 ^ (prefixWord ++ tailWord_4373661).sum := by decide
  have hdescent : baseEnd_4373661 < baseStart_4373661 := by decide
  rcases family_descends (prefixWord ++ tailWord_4373661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4373666 : List Nat := [3, 3, 1, 3, 2, 2, 2, 1, 2, 2, 2]
def baseStart_4373666 : Nat := 118140960795 + 4373666 * 2 ^ 59
def prefixEnd_4373666 : Nat := 4983230072969 + 3 ^ 40 * 4373666 * 2
def baseEnd_4373666 : Nat := 2245792880227390245360883

theorem tailTrace_4373666 : CollatzResearch.WordTrace tailWord_4373666 prefixEnd_4373666 2245792880227390245360883 := by
  unfold tailWord_4373666
  simp only [CollatzResearch.WordTrace]
  refine ⟨39880176043240629882293213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106347136115308346352781901 39880176043240629882293213)
  ·
    refine ⟨14955066016215236205859955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39880176043240629882293213 14955066016215236205859955)
    ·
      refine ⟨22432599024322854308789933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14955066016215236205859955 22432599024322854308789933)
      ·
        refine ⟨8412224634121070365796225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22432599024322854308789933 8412224634121070365796225)
        ·
          refine ⟨6309168475590802774347169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8412224634121070365796225 6309168475590802774347169)
          ·
            refine ⟨4731876356693102080760377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6309168475590802774347169 4731876356693102080760377)
            ·
              refine ⟨3548907267519826560570283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4731876356693102080760377 3548907267519826560570283)
              ·
                refine ⟨5323360901279739840855425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3548907267519826560570283 5323360901279739840855425)
                ·
                  refine ⟨3992520675959804880641569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5323360901279739840855425 3992520675959804880641569)
                  ·
                    refine ⟨2994390506969853660481177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3992520675959804880641569 2994390506969853660481177)
                    ·
                      refine ⟨2245792880227390245360883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2994390506969853660481177 2245792880227390245360883)
                      ·
                        rfl

theorem cell23_4373666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_4373666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4373666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4373666 prefixEnd_4373666 := by exact prefixLift 4373666
  have htrace : WordTrace (prefixWord ++ tailWord_4373666) baseStart_4373666 baseEnd_4373666 := by
    simpa [prefixWord, tailWord_4373666, baseEnd_4373666] using wordTrace_append hprefix tailTrace_4373666
  have hstable : (prefixWord ++ tailWord_4373666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4373666).length < 2 ^ (prefixWord ++ tailWord_4373666).sum := by decide
  have hdescent : baseEnd_4373666 < baseStart_4373666 := by decide
  rcases family_descends (prefixWord ++ tailWord_4373666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4373721 : List Nat := [1, 2, 1, 2, 3, 1, 1, 2, 2, 5, 3]
def baseStart_4373721 : Nat := 118140960795 + 4373721 * 2 ^ 59
def prefixEnd_4373721 : Nat := 4983230072969 + 3 ^ 40 * 4373721 * 2
def baseEnd_4373721 : Nat := 2245821121663387530173129

theorem tailTrace_4373721 : CollatzResearch.WordTrace tailWord_4373721 prefixEnd_4373721 2245821121663387530173129 := by
  unfold tailWord_4373721
  simp only [CollatzResearch.WordTrace]
  refine ⟨159522710187763263922425017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106348473458508842614950011 159522710187763263922425017)
  ·
    refine ⟨119642032640822447941818763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159522710187763263922425017 119642032640822447941818763)
    ·
      refine ⟨179463048961233671912728145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119642032640822447941818763 179463048961233671912728145)
      ·
        refine ⟨134597286720925253934546109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179463048961233671912728145 134597286720925253934546109)
        ·
          refine ⟨50473982520346970225454791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134597286720925253934546109 50473982520346970225454791)
          ·
            refine ⟨75710973780520455338182187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50473982520346970225454791 75710973780520455338182187)
            ·
              refine ⟨113566460670780683007273281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75710973780520455338182187 113566460670780683007273281)
              ·
                refine ⟨85174845503085512255454961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113566460670780683007273281 85174845503085512255454961)
                ·
                  refine ⟨63881134127314134191591221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85174845503085512255454961 63881134127314134191591221)
                  ·
                    refine ⟨5988856324435700080461677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 63881134127314134191591221 5988856324435700080461677)
                    ·
                      refine ⟨2245821121663387530173129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5988856324435700080461677 2245821121663387530173129)
                      ·
                        rfl

theorem cell23_4373721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 5, 3].length) (baseStart_4373721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4373721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4373721 prefixEnd_4373721 := by exact prefixLift 4373721
  have htrace : WordTrace (prefixWord ++ tailWord_4373721) baseStart_4373721 baseEnd_4373721 := by
    simpa [prefixWord, tailWord_4373721, baseEnd_4373721] using wordTrace_append hprefix tailTrace_4373721
  have hstable : (prefixWord ++ tailWord_4373721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4373721).length < 2 ^ (prefixWord ++ tailWord_4373721).sum := by decide
  have hdescent : baseEnd_4373721 < baseStart_4373721 := by decide
  rcases family_descends (prefixWord ++ tailWord_4373721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4373762 : List Nat := [3, 4, 1, 1, 3, 2, 1, 2, 6]
def baseStart_4373762 : Nat := 118140960795 + 4373762 * 2 ^ 59
def prefixEnd_4373762 : Nat := 4983230072969 + 3 ^ 40 * 4373762 * 2
def baseEnd_4373762 : Nat := 249538019374469096640049

theorem tailTrace_4373762 : CollatzResearch.WordTrace tailWord_4373762 prefixEnd_4373762 249538019374469096640049 := by
  unfold tailWord_4373762
  simp only [CollatzResearch.WordTrace]
  refine ⟨39881051395153681981166885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106349470387076485283111693 39881051395153681981166885)
  ·
    refine ⟨7477697136591315371468791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39881051395153681981166885 7477697136591315371468791)
    ·
      refine ⟨11216545704886973057203187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7477697136591315371468791 11216545704886973057203187)
      ·
        refine ⟨16824818557330459585804781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11216545704886973057203187 16824818557330459585804781)
        ·
          refine ⟨6309306958998922344676793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16824818557330459585804781 6309306958998922344676793)
          ·
            refine ⟨4731980219249191758507595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6309306958998922344676793 4731980219249191758507595)
            ·
              refine ⟨7097970328873787637761393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4731980219249191758507595 7097970328873787637761393)
              ·
                refine ⟨5323477746655340728321045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7097970328873787637761393 5323477746655340728321045)
                ·
                  refine ⟨249538019374469096640049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5323477746655340728321045 249538019374469096640049)
                  ·
                    rfl

theorem cell23_4373762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_4373762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4373762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4373762 prefixEnd_4373762 := by exact prefixLift 4373762
  have htrace : WordTrace (prefixWord ++ tailWord_4373762) baseStart_4373762 baseEnd_4373762 := by
    simpa [prefixWord, tailWord_4373762, baseEnd_4373762] using wordTrace_append hprefix tailTrace_4373762
  have hstable : (prefixWord ++ tailWord_4373762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4373762).length < 2 ^ (prefixWord ++ tailWord_4373762).sum := by decide
  have hdescent : baseEnd_4373762 < baseStart_4373762 := by decide
  rcases family_descends (prefixWord ++ tailWord_4373762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4373772 : List Nat := [2, 2, 1, 2, 2, 3, 2, 4, 1, 1, 3]
def baseStart_4373772 : Nat := 118140960795 + 4373772 * 2 ^ 59
def prefixEnd_4373772 : Nat := 4983230072969 + 3 ^ 40 * 4373772 * 2
def baseEnd_4373772 : Nat := 2245847309176766830635395

theorem tailTrace_4373772 : CollatzResearch.WordTrace tailWord_4373772 prefixEnd_4373772 2245847309176766830635395 := by
  unfold tailWord_4373772
  simp only [CollatzResearch.WordTrace]
  refine ⟨79762285155289249816265785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106349713540385666421687713 79762285155289249816265785)
  ·
    refine ⟨59821713866466937362199339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79762285155289249816265785 59821713866466937362199339)
    ·
      refine ⟨89732570799700406043299009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59821713866466937362199339 89732570799700406043299009)
      ·
        refine ⟨67299428099775304532474257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89732570799700406043299009 67299428099775304532474257)
        ·
          refine ⟨50474571074831478399355693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67299428099775304532474257 50474571074831478399355693)
          ·
            refine ⟨18927964153061804399758385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50474571074831478399355693 18927964153061804399758385)
            ·
              refine ⟨14195973114796353299818789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18927964153061804399758385 14195973114796353299818789)
              ·
                refine ⟨2661744959024316243716023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14195973114796353299818789 2661744959024316243716023)
                ·
                  refine ⟨3992617438536474365574035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2661744959024316243716023 3992617438536474365574035)
                  ·
                    refine ⟨5988926157804711548361053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3992617438536474365574035 5988926157804711548361053)
                    ·
                      refine ⟨2245847309176766830635395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5988926157804711548361053 2245847309176766830635395)
                      ·
                        rfl

theorem cell23_4373772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 4, 1, 1, 3].length) (baseStart_4373772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4373772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4373772 prefixEnd_4373772 := by exact prefixLift 4373772
  have htrace : WordTrace (prefixWord ++ tailWord_4373772) baseStart_4373772 baseEnd_4373772 := by
    simpa [prefixWord, tailWord_4373772, baseEnd_4373772] using wordTrace_append hprefix tailTrace_4373772
  have hstable : (prefixWord ++ tailWord_4373772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4373772).length < 2 ^ (prefixWord ++ tailWord_4373772).sum := by decide
  have hdescent : baseEnd_4373772 < baseStart_4373772 := by decide
  rcases family_descends (prefixWord ++ tailWord_4373772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4373788 : List Nat := [2, 2, 3, 1, 1, 1, 5, 1, 1, 6]
def baseStart_4373788 : Nat := 118140960795 + 4373788 * 2 ^ 59
def prefixEnd_4373788 : Nat := 4983230072969 + 3 ^ 40 * 4373788 * 2
def baseEnd_4373788 : Nat := 748618508289079589345107

theorem tailTrace_4373788 : CollatzResearch.WordTrace tailWord_4373788 prefixEnd_4373788 748618508289079589345107 := by
  unfold tailWord_4373788
  simp only [CollatzResearch.WordTrace]
  refine ⟨79762576939260267182557009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106350102585680356243409345 79762576939260267182557009)
  ·
    refine ⟨59821932704445200386917757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79762576939260267182557009 59821932704445200386917757)
    ·
      refine ⟨22433224764166950145094159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59821932704445200386917757 22433224764166950145094159)
      ·
        refine ⟨33649837146250425217641239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22433224764166950145094159 33649837146250425217641239)
        ·
          refine ⟨50474755719375637826461859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33649837146250425217641239 50474755719375637826461859)
          ·
            refine ⟨75712133579063456739692789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50474755719375637826461859 75712133579063456739692789)
            ·
              refine ⟨7098012523037199069346199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 75712133579063456739692789 7098012523037199069346199)
              ·
                refine ⟨10647018784555798604019299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7098012523037199069346199 10647018784555798604019299)
                ·
                  refine ⟨15970528176833697906028949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10647018784555798604019299 15970528176833697906028949)
                  ·
                    refine ⟨748618508289079589345107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15970528176833697906028949 748618508289079589345107)
                    ·
                      rfl

theorem cell23_4373788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 1, 1, 6].length) (baseStart_4373788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4373788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4373788 prefixEnd_4373788 := by exact prefixLift 4373788
  have htrace : WordTrace (prefixWord ++ tailWord_4373788) baseStart_4373788 baseEnd_4373788 := by
    simpa [prefixWord, tailWord_4373788, baseEnd_4373788] using wordTrace_append hprefix tailTrace_4373788
  have hstable : (prefixWord ++ tailWord_4373788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4373788).length < 2 ^ (prefixWord ++ tailWord_4373788).sum := by decide
  have hdescent : baseEnd_4373788 < baseStart_4373788 := by decide
  rcases family_descends (prefixWord ++ tailWord_4373788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4373795 : List Nat := [1, 1, 1, 4, 2, 4, 2, 2, 1, 1, 4]
def baseStart_4373795 : Nat := 118140960795 + 4373795 * 2 ^ 59
def prefixEnd_4373795 : Nat := 4983230072969 + 3 ^ 40 * 4373795 * 2
def baseEnd_4373795 : Nat := 2245859119231820240647789

theorem tailTrace_4373795 : CollatzResearch.WordTrace tailWord_4373795 prefixEnd_4373795 2245859119231820240647789 := by
  unfold tailWord_4373795
  simp only [CollatzResearch.WordTrace]
  refine ⟨159525409189495174560618839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106350272792996783040412559 159525409189495174560618839)
  ·
    refine ⟨239288113784242761840928259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159525409189495174560618839 239288113784242761840928259)
    ·
      refine ⟨358932170676364142761392389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239288113784242761840928259 358932170676364142761392389)
      ·
        refine ⟨67299782001818276767761073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 358932170676364142761392389 67299782001818276767761073)
        ·
          refine ⟨50474836501363707575820805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67299782001818276767761073 50474836501363707575820805)
          ·
            refine ⟨9464031844005695170466401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50474836501363707575820805 9464031844005695170466401)
            ·
              refine ⟨7098023883004271377849801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9464031844005695170466401 7098023883004271377849801)
              ·
                refine ⟨5323517912253203533387351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7098023883004271377849801 5323517912253203533387351)
                ·
                  refine ⟨7985276868379805300081027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5323517912253203533387351 7985276868379805300081027)
                  ·
                    refine ⟨11977915302569707950121541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7985276868379805300081027 11977915302569707950121541)
                    ·
                      refine ⟨2245859119231820240647789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11977915302569707950121541 2245859119231820240647789)
                      ·
                        rfl

theorem cell23_4373795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 2, 1, 1, 4].length) (baseStart_4373795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4373795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4373795 prefixEnd_4373795 := by exact prefixLift 4373795
  have htrace : WordTrace (prefixWord ++ tailWord_4373795) baseStart_4373795 baseEnd_4373795 := by
    simpa [prefixWord, tailWord_4373795, baseEnd_4373795] using wordTrace_append hprefix tailTrace_4373795
  have hstable : (prefixWord ++ tailWord_4373795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4373795).length < 2 ^ (prefixWord ++ tailWord_4373795).sum := by decide
  have hdescent : baseEnd_4373795 < baseStart_4373795 := by decide
  rcases family_descends (prefixWord ++ tailWord_4373795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4373846 : List Nat := [5, 2, 3, 1, 1, 1, 1, 1, 3, 1, 4]
def baseStart_4373846 : Nat := 118140960795 + 4373846 * 2 ^ 59
def prefixEnd_4373846 : Nat := 4983230072969 + 3 ^ 40 * 4373846 * 2
def baseEnd_4373846 : Nat := 2245885306745199541110055

theorem tailTrace_4373846 : CollatzResearch.WordTrace tailWord_4373846 prefixEnd_4373846 2245885306745199541110055 := by
  unfold tailWord_4373846
  simp only [CollatzResearch.WordTrace]
  refine ⟨9970454332019400641920337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 106351512874873606847150261 9970454332019400641920337)
  ·
    refine ⟨7477840749014550481440253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9970454332019400641920337 7477840749014550481440253)
    ·
      refine ⟨2804190280880456430540095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7477840749014550481440253 2804190280880456430540095)
      ·
        refine ⟨4206285421320684645810143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2804190280880456430540095 4206285421320684645810143)
        ·
          refine ⟨6309428131981026968715215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4206285421320684645810143 6309428131981026968715215)
          ·
            refine ⟨9464142197971540453072823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6309428131981026968715215 9464142197971540453072823)
            ·
              refine ⟨14196213296957310679609235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9464142197971540453072823 14196213296957310679609235)
              ·
                refine ⟨21294319945435966019413853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14196213296957310679609235 21294319945435966019413853)
                ·
                  refine ⟨7985369979538487257280195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21294319945435966019413853 7985369979538487257280195)
                  ·
                    refine ⟨11978054969307730885920293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7985369979538487257280195 11978054969307730885920293)
                    ·
                      refine ⟨2245885306745199541110055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11978054969307730885920293 2245885306745199541110055)
                      ·
                        rfl

theorem cell23_4373846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_4373846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4373846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4373846 prefixEnd_4373846 := by exact prefixLift 4373846
  have htrace : WordTrace (prefixWord ++ tailWord_4373846) baseStart_4373846 baseEnd_4373846 := by
    simpa [prefixWord, tailWord_4373846, baseEnd_4373846] using wordTrace_append hprefix tailTrace_4373846
  have hstable : (prefixWord ++ tailWord_4373846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4373846).length < 2 ^ (prefixWord ++ tailWord_4373846).sum := by decide
  have hdescent : baseEnd_4373846 < baseStart_4373846 := by decide
  rcases family_descends (prefixWord ++ tailWord_4373846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4373885 : List Nat := [1, 4, 1, 1, 2, 2, 1, 2, 3, 4, 2]
def baseStart_4373885 : Nat := 118140960795 + 4373885 * 2 ^ 59
def prefixEnd_4373885 : Nat := 4983230072969 + 3 ^ 40 * 4373885 * 2
def baseEnd_4373885 : Nat := 2245905332490724888522375

theorem tailTrace_4373885 : CollatzResearch.WordTrace tailWord_4373885 prefixEnd_4373885 2245905332490724888522375 := by
  unfold tailWord_4373885
  simp only [CollatzResearch.WordTrace]
  refine ⟨159528691759169119931395109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106352461172779413287596739 159528691759169119931395109)
  ·
    refine ⟨29911629704844209987136583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 159528691759169119931395109 29911629704844209987136583)
    ·
      refine ⟨44867444557266314980704875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29911629704844209987136583 44867444557266314980704875)
      ·
        refine ⟨67301166835899472471057313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44867444557266314980704875 67301166835899472471057313)
        ·
          refine ⟨50475875126924604353292985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67301166835899472471057313 50475875126924604353292985)
          ·
            refine ⟨37856906345193453264969739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50475875126924604353292985 37856906345193453264969739)
            ·
              refine ⟨56785359517790179897454609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37856906345193453264969739 56785359517790179897454609)
              ·
                refine ⟨42589019638342634923090957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56785359517790179897454609 42589019638342634923090957)
                ·
                  refine ⟨15970882364378488096159109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42589019638342634923090957 15970882364378488096159109)
                  ·
                    refine ⟨2994540443320966518029833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15970882364378488096159109 2994540443320966518029833)
                    ·
                      refine ⟨2245905332490724888522375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2994540443320966518029833 2245905332490724888522375)
                      ·
                        rfl

theorem cell23_4373885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 3, 4, 2].length) (baseStart_4373885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4373885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4373885 prefixEnd_4373885 := by exact prefixLift 4373885
  have htrace : WordTrace (prefixWord ++ tailWord_4373885) baseStart_4373885 baseEnd_4373885 := by
    simpa [prefixWord, tailWord_4373885, baseEnd_4373885] using wordTrace_append hprefix tailTrace_4373885
  have hstable : (prefixWord ++ tailWord_4373885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4373885).length < 2 ^ (prefixWord ++ tailWord_4373885).sum := by decide
  have hdescent : baseEnd_4373885 < baseStart_4373885 := by decide
  rcases family_descends (prefixWord ++ tailWord_4373885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4373975 : List Nat := [1, 1, 3, 2, 1, 1, 1, 4, 1, 6, 2]
def baseStart_4373975 : Nat := 118140960795 + 4373975 * 2 ^ 59
def prefixEnd_4373975 : Nat := 4983230072969 + 3 ^ 40 * 4373975 * 2
def baseEnd_4373975 : Nat := 2245951545749629536396961

theorem tailTrace_4373975 : CollatzResearch.WordTrace tailWord_4373975 prefixEnd_4373975 2245951545749629536396961 := by
  unfold tailWord_4373975
  simp only [CollatzResearch.WordTrace]
  refine ⟨159531974328843065302171379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106354649552562043534780919 159531974328843065302171379)
  ·
    refine ⟨239297961493264597953257069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159531974328843065302171379 239297961493264597953257069)
    ·
      refine ⟨89736735559974224232471401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 239297961493264597953257069 89736735559974224232471401)
      ·
        refine ⟨67302551669980668174353551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89736735559974224232471401 67302551669980668174353551)
        ·
          refine ⟨100953827504971002261530327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67302551669980668174353551 100953827504971002261530327)
          ·
            refine ⟨151430741257456503392295491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100953827504971002261530327 151430741257456503392295491)
            ·
              refine ⟨227146111886184755088443237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151430741257456503392295491 227146111886184755088443237)
              ·
                refine ⟨42589895978659641579083107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 227146111886184755088443237 42589895978659641579083107)
                ·
                  refine ⟨63884843967989462368624661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42589895978659641579083107 63884843967989462368624661)
                  ·
                    refine ⟨2994602060999506048529281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 63884843967989462368624661 2994602060999506048529281)
                    ·
                      refine ⟨2245951545749629536396961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2994602060999506048529281 2245951545749629536396961)
                      ·
                        rfl

theorem cell23_4373975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 6, 2].length) (baseStart_4373975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4373975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4373975 prefixEnd_4373975 := by exact prefixLift 4373975
  have htrace : WordTrace (prefixWord ++ tailWord_4373975) baseStart_4373975 baseEnd_4373975 := by
    simpa [prefixWord, tailWord_4373975, baseEnd_4373975] using wordTrace_append hprefix tailTrace_4373975
  have hstable : (prefixWord ++ tailWord_4373975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4373975).length < 2 ^ (prefixWord ++ tailWord_4373975).sum := by decide
  have hdescent : baseEnd_4373975 < baseStart_4373975 := by decide
  rcases family_descends (prefixWord ++ tailWord_4373975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4373988 : List Nat := [2, 3, 1, 1, 1, 1, 1, 3, 1, 3, 6]
def baseStart_4373988 : Nat := 118140960795 + 4373988 * 2 ^ 59
def prefixEnd_4373988 : Nat := 4983230072969 + 3 ^ 40 * 4373988 * 2
def baseEnd_4373988 : Nat := 2245958220998137985534401

theorem tailTrace_4373988 : CollatzResearch.WordTrace tailWord_4373988 prefixEnd_4373988 2245958220998137985534401 := by
  unfold tailWord_4373988
  simp only [CollatzResearch.WordTrace]
  refine ⟨79766224238897984261197309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106354965651863979014929745 79766224238897984261197309)
  ·
    refine ⟨29912334089586744097948991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79766224238897984261197309 29912334089586744097948991)
    ·
      refine ⟨44868501134380116146923487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29912334089586744097948991 44868501134380116146923487)
      ·
        refine ⟨67302751701570174220385231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44868501134380116146923487 67302751701570174220385231)
        ·
          refine ⟨100954127552355261330577847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67302751701570174220385231 100954127552355261330577847)
          ·
            refine ⟨151431191328532891995866771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100954127552355261330577847 151431191328532891995866771)
            ·
              refine ⟨227146786992799337993800157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151431191328532891995866771 227146786992799337993800157)
              ·
                refine ⟨85180045122299751747675059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 227146786992799337993800157 85180045122299751747675059)
                ·
                  refine ⟨127770067683449627621512589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85180045122299751747675059 127770067683449627621512589)
                  ·
                    refine ⟨47913775381293610358067221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 127770067683449627621512589 47913775381293610358067221)
                    ·
                      refine ⟨2245958220998137985534401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47913775381293610358067221 2245958220998137985534401)
                      ·
                        rfl

theorem cell23_4373988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_4373988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4373988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4373988 prefixEnd_4373988 := by exact prefixLift 4373988
  have htrace : WordTrace (prefixWord ++ tailWord_4373988) baseStart_4373988 baseEnd_4373988 := by
    simpa [prefixWord, tailWord_4373988, baseEnd_4373988] using wordTrace_append hprefix tailTrace_4373988
  have hstable : (prefixWord ++ tailWord_4373988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4373988).length < 2 ^ (prefixWord ++ tailWord_4373988).sum := by decide
  have hdescent : baseEnd_4373988 < baseStart_4373988 := by decide
  rcases family_descends (prefixWord ++ tailWord_4373988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4374062 : List Nat := [4, 1, 3, 1, 2, 1, 1, 2, 3, 5]
def baseStart_4374062 : Nat := 118140960795 + 4374062 * 2 ^ 59
def prefixEnd_4374062 : Nat := 4983230072969 + 3 ^ 40 * 4374062 * 2
def baseEnd_4374062 : Nat := 748665406188856898669687

theorem tailTrace_4374062 : CollatzResearch.WordTrace tailWord_4374062 prefixEnd_4374062 748665406188856898669687 := by
  unfold tailWord_4374062
  simp only [CollatzResearch.WordTrace]
  refine ⟨19941893434940984895073555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106356764986351919440392293 19941893434940984895073555)
  ·
    refine ⟨29912840152411477342610333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19941893434940984895073555 29912840152411477342610333)
    ·
      refine ⟨11217315057154304003478875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29912840152411477342610333 11217315057154304003478875)
      ·
        refine ⟨16825972585731456005218313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11217315057154304003478875 16825972585731456005218313)
        ·
          refine ⟨12619479439298592003913735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16825972585731456005218313 12619479439298592003913735)
          ·
            refine ⟨18929219158947888005870603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12619479439298592003913735 18929219158947888005870603)
            ·
              refine ⟨28393828738421832008805905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18929219158947888005870603 28393828738421832008805905)
              ·
                refine ⟨21295371553816374006604429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28393828738421832008805905 21295371553816374006604429)
                ·
                  refine ⟨7985764332681140252476661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21295371553816374006604429 7985764332681140252476661)
                  ·
                    refine ⟨748665406188856898669687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7985764332681140252476661 748665406188856898669687)
                    ·
                      rfl

theorem cell23_4374062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_4374062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4374062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4374062 prefixEnd_4374062 := by exact prefixLift 4374062
  have htrace : WordTrace (prefixWord ++ tailWord_4374062) baseStart_4374062 baseEnd_4374062 := by
    simpa [prefixWord, tailWord_4374062, baseEnd_4374062] using wordTrace_append hprefix tailTrace_4374062
  have hstable : (prefixWord ++ tailWord_4374062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4374062).length < 2 ^ (prefixWord ++ tailWord_4374062).sum := by decide
  have hdescent : baseEnd_4374062 < baseStart_4374062 := by decide
  rcases family_descends (prefixWord ++ tailWord_4374062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4374116 : List Nat := [2, 3, 1, 1, 2, 4, 2, 1, 3, 2, 2]
def baseStart_4374116 : Nat := 118140960795 + 4374116 * 2 ^ 59
def prefixEnd_4374116 : Nat := 4983230072969 + 3 ^ 40 * 4374116 * 2
def baseEnd_4374116 : Nat := 2246023946521913484733813

theorem tailTrace_4374116 : CollatzResearch.WordTrace tailWord_4374116 prefixEnd_4374116 2246023946521913484733813 := by
  unfold tailWord_4374116
  simp only [CollatzResearch.WordTrace]
  refine ⟨79768558510666123191527101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106358078014221497588702801 79768558510666123191527101)
  ·
    refine ⟨29913209441499796196822663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79768558510666123191527101 29913209441499796196822663)
    ·
      refine ⟨44869814162249694295233995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29913209441499796196822663 44869814162249694295233995)
      ·
        refine ⟨67304721243374541442850993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44869814162249694295233995 67304721243374541442850993)
        ·
          refine ⟨50478540932530906082138245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67304721243374541442850993 50478540932530906082138245)
          ·
            refine ⟨9464726424849544890400921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50478540932530906082138245 9464726424849544890400921)
            ·
              refine ⟨7098544818637158667800691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9464726424849544890400921 7098544818637158667800691)
              ·
                refine ⟨10647817227955738001701037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7098544818637158667800691 10647817227955738001701037)
                ·
                  refine ⟨3992931460483401750637889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10647817227955738001701037 3992931460483401750637889)
                  ·
                    refine ⟨2994698595362551312978417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3992931460483401750637889 2994698595362551312978417)
                    ·
                      refine ⟨2246023946521913484733813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2994698595362551312978417 2246023946521913484733813)
                      ·
                        rfl

theorem cell23_4374116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 1, 3, 2, 2].length) (baseStart_4374116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4374116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4374116 prefixEnd_4374116 := by exact prefixLift 4374116
  have htrace : WordTrace (prefixWord ++ tailWord_4374116) baseStart_4374116 baseEnd_4374116 := by
    simpa [prefixWord, tailWord_4374116, baseEnd_4374116] using wordTrace_append hprefix tailTrace_4374116
  have hstable : (prefixWord ++ tailWord_4374116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4374116).length < 2 ^ (prefixWord ++ tailWord_4374116).sum := by decide
  have hdescent : baseEnd_4374116 < baseStart_4374116 := by decide
  rcases family_descends (prefixWord ++ tailWord_4374116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4374126 : List Nat := [4, 1, 2, 2, 4, 1, 1, 1, 1, 6]
def baseStart_4374126 : Nat := 118140960795 + 4374126 * 2 ^ 59
def prefixEnd_4374126 : Nat := 4983230072969 + 3 ^ 40 * 4374126 * 2
def baseEnd_4374126 : Nat := 748676360442819481869589

theorem tailTrace_4374126 : CollatzResearch.WordTrace tailWord_4374126 prefixEnd_4374126 748676360442819481869589 := by
  unfold tailWord_4374126
  simp only [CollatzResearch.WordTrace]
  refine ⟨19942185218912002261364779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106358321167530678727278821 19942185218912002261364779)
  ·
    refine ⟨29913277828368003392047169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19942185218912002261364779 29913277828368003392047169)
    ·
      refine ⟨22434958371276002544035377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29913277828368003392047169 22434958371276002544035377)
      ·
        refine ⟨16826218778457001908026533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22434958371276002544035377 16826218778457001908026533)
        ·
          refine ⟨3154916020960687857754975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16826218778457001908026533 3154916020960687857754975)
          ·
            refine ⟨4732374031441031786632463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3154916020960687857754975 4732374031441031786632463)
            ·
              refine ⟨7098561047161547679948695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4732374031441031786632463 7098561047161547679948695)
              ·
                refine ⟨10647841570742321519923043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7098561047161547679948695 10647841570742321519923043)
                ·
                  refine ⟨15971762356113482279884565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10647841570742321519923043 15971762356113482279884565)
                  ·
                    refine ⟨748676360442819481869589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15971762356113482279884565 748676360442819481869589)
                    ·
                      rfl

theorem cell23_4374126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 1, 1, 6].length) (baseStart_4374126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4374126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4374126 prefixEnd_4374126 := by exact prefixLift 4374126
  have htrace : WordTrace (prefixWord ++ tailWord_4374126) baseStart_4374126 baseEnd_4374126 := by
    simpa [prefixWord, tailWord_4374126, baseEnd_4374126] using wordTrace_append hprefix tailTrace_4374126
  have hstable : (prefixWord ++ tailWord_4374126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4374126).length < 2 ^ (prefixWord ++ tailWord_4374126).sum := by decide
  have hdescent : baseEnd_4374126 < baseStart_4374126 := by decide
  rcases family_descends (prefixWord ++ tailWord_4374126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4374165 : List Nat := [1, 3, 2, 1, 1, 1, 1, 3, 4, 6]
def baseStart_4374165 : Nat := 118140960795 + 4374165 * 2 ^ 59
def prefixEnd_4374165 : Nat := 4983230072969 + 3 ^ 40 * 4374165 * 2
def baseEnd_4374165 : Nat := 748683035691327931007029

theorem tailTrace_4374165 : CollatzResearch.WordTrace tailWord_4374165 prefixEnd_4374165 748683035691327931007029 := by
  unfold tailWord_4374165
  simp only [CollatzResearch.WordTrace]
  refine ⟨159538904198154727751587949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106359269465436485167725299 159538904198154727751587949)
  ·
    refine ⟨59827089074308022906845481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159538904198154727751587949 59827089074308022906845481)
    ·
      refine ⟨44870316805731017180134111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59827089074308022906845481 44870316805731017180134111)
      ·
        refine ⟨67305475208596525770201167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44870316805731017180134111 67305475208596525770201167)
        ·
          refine ⟨100958212812894788655301751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67305475208596525770201167 100958212812894788655301751)
          ·
            refine ⟨151437319219342182982952627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100958212812894788655301751 151437319219342182982952627)
            ·
              refine ⟨227155978829013274474428941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151437319219342182982952627 227155978829013274474428941)
              ·
                refine ⟨85183492060879977927910853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 227155978829013274474428941 85183492060879977927910853)
                ·
                  refine ⟨15971904761414995861483285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 85183492060879977927910853 15971904761414995861483285)
                  ·
                    refine ⟨748683035691327931007029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15971904761414995861483285 748683035691327931007029)
                    ·
                      rfl

theorem cell23_4374165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 4, 6].length) (baseStart_4374165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4374165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4374165 prefixEnd_4374165 := by exact prefixLift 4374165
  have htrace : WordTrace (prefixWord ++ tailWord_4374165) baseStart_4374165 baseEnd_4374165 := by
    simpa [prefixWord, tailWord_4374165, baseEnd_4374165] using wordTrace_append hprefix tailTrace_4374165
  have hstable : (prefixWord ++ tailWord_4374165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4374165).length < 2 ^ (prefixWord ++ tailWord_4374165).sum := by decide
  have hdescent : baseEnd_4374165 < baseStart_4374165 := by decide
  rcases family_descends (prefixWord ++ tailWord_4374165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4374195 : List Nat := [1, 1, 1, 2, 3, 3, 2, 1, 9]
def baseStart_4374195 : Nat := 118140960795 + 4374195 * 2 ^ 59
def prefixEnd_4374195 : Nat := 4983230072969 + 3 ^ 40 * 4374195 * 2
def baseEnd_4374195 : Nat := 249562723499290963960661

theorem tailTrace_4374195 : CollatzResearch.WordTrace tailWord_4374195 prefixEnd_4374195 249562723499290963960661 := by
  unfold tailWord_4374195
  simp only [CollatzResearch.WordTrace]
  refine ⟨159539998388046042875180039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106359998925364028583453359 159539998388046042875180039)
  ·
    refine ⟨239309997582069064312770059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159539998388046042875180039 239309997582069064312770059)
    ·
      refine ⟨358964996373103596469155089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239309997582069064312770059 358964996373103596469155089)
      ·
        refine ⟨269223747279827697351866317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 358964996373103596469155089 269223747279827697351866317)
        ·
          refine ⟨100958905229935386506949869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 269223747279827697351866317 100958905229935386506949869)
          ·
            refine ⟨37859589461225769940106201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100958905229935386506949869 37859589461225769940106201)
            ·
              refine ⟨28394692095919327455079651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37859589461225769940106201 28394692095919327455079651)
              ·
                refine ⟨42592038143878991182619477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28394692095919327455079651 42592038143878991182619477)
                ·
                  refine ⟨249562723499290963960661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 42592038143878991182619477 249562723499290963960661)
                  ·
                    rfl

theorem cell23_4374195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 9].length) (baseStart_4374195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4374195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4374195 prefixEnd_4374195 := by exact prefixLift 4374195
  have htrace : WordTrace (prefixWord ++ tailWord_4374195) baseStart_4374195 baseEnd_4374195 := by
    simpa [prefixWord, tailWord_4374195, baseEnd_4374195] using wordTrace_append hprefix tailTrace_4374195
  have hstable : (prefixWord ++ tailWord_4374195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4374195).length < 2 ^ (prefixWord ++ tailWord_4374195).sum := by decide
  have hdescent : baseEnd_4374195 < baseStart_4374195 := by decide
  rcases family_descends (prefixWord ++ tailWord_4374195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4374206 : List Nat := [4, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2]
def baseStart_4374206 : Nat := 118140960795 + 4374206 * 2 ^ 59
def prefixEnd_4374206 : Nat := 4983230072969 + 3 ^ 40 * 4374206 * 2
def baseEnd_4374206 : Nat := 2246070159780818132608399

theorem tailTrace_4374206 : CollatzResearch.WordTrace tailWord_4374206 prefixEnd_4374206 2246070159780818132608399 := by
  unfold tailWord_4374206
  simp only [CollatzResearch.WordTrace]
  refine ⟨19942549948875773969228809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106360266394004127835886981 19942549948875773969228809)
  ·
    refine ⟨14956912461656830476921607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19942549948875773969228809 14956912461656830476921607)
    ·
      refine ⟨22435368692485245715382411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14956912461656830476921607 22435368692485245715382411)
      ·
        refine ⟨33653053038727868573073617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22435368692485245715382411 33653053038727868573073617)
        ·
          refine ⟨25239789779045901429805213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33653053038727868573073617 25239789779045901429805213)
          ·
            refine ⟨9464921167142213036176955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25239789779045901429805213 9464921167142213036176955)
            ·
              refine ⟨14197381750713319554265433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9464921167142213036176955 14197381750713319554265433)
              ·
                refine ⟨10648036313034989665699075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14197381750713319554265433 10648036313034989665699075)
                ·
                  refine ⟨15972054469552484498548613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10648036313034989665699075 15972054469552484498548613)
                  ·
                    refine ⟨2994760213041090843477865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15972054469552484498548613 2994760213041090843477865)
                    ·
                      refine ⟨2246070159780818132608399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2994760213041090843477865 2246070159780818132608399)
                      ·
                        rfl

theorem cell23_4374206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2].length) (baseStart_4374206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4374206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4374206 prefixEnd_4374206 := by exact prefixLift 4374206
  have htrace : WordTrace (prefixWord ++ tailWord_4374206) baseStart_4374206 baseEnd_4374206 := by
    simpa [prefixWord, tailWord_4374206, baseEnd_4374206] using wordTrace_append hprefix tailTrace_4374206
  have hstable : (prefixWord ++ tailWord_4374206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4374206).length < 2 ^ (prefixWord ++ tailWord_4374206).sum := by decide
  have hdescent : baseEnd_4374206 < baseStart_4374206 := by decide
  rcases family_descends (prefixWord ++ tailWord_4374206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4374236 : List Nat := [2, 2, 5, 1, 2, 1, 1, 1, 2, 2, 4]
def baseStart_4374236 : Nat := 118140960795 + 4374236 * 2 ^ 59
def prefixEnd_4374236 : Nat := 4983230072969 + 3 ^ 40 * 4374236 * 2
def baseEnd_4374236 : Nat := 2246085564200453015233261

theorem tailTrace_4374236 : CollatzResearch.WordTrace tailWord_4374236 prefixEnd_4374236 2246085564200453015233261 := by
  unfold tailWord_4374236
  simp only [CollatzResearch.WordTrace]
  refine ⟨79770746890448753438711281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106360995853931671251615041 79770746890448753438711281)
  ·
    refine ⟨59828060167836565079033461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79770746890448753438711281 59828060167836565079033461)
    ·
      refine ⟨5608880640734677976159387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59828060167836565079033461 5608880640734677976159387)
      ·
        refine ⟨8413320961102016964239081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5608880640734677976159387 8413320961102016964239081)
        ·
          refine ⟨6309990720826512723179311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8413320961102016964239081 6309990720826512723179311)
          ·
            refine ⟨9464986081239769084768967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6309990720826512723179311 9464986081239769084768967)
            ·
              refine ⟨14197479121859653627153451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9464986081239769084768967 14197479121859653627153451)
              ·
                refine ⟨21296218682789480440730177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14197479121859653627153451 21296218682789480440730177)
                ·
                  refine ⟨15972164012092110330547633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21296218682789480440730177 15972164012092110330547633)
                  ·
                    refine ⟨11979123009069082747910725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15972164012092110330547633 11979123009069082747910725)
                    ·
                      refine ⟨2246085564200453015233261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11979123009069082747910725 2246085564200453015233261)
                      ·
                        rfl

theorem cell23_4374236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_4374236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4374236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4374236 prefixEnd_4374236 := by exact prefixLift 4374236
  have htrace : WordTrace (prefixWord ++ tailWord_4374236) baseStart_4374236 baseEnd_4374236 := by
    simpa [prefixWord, tailWord_4374236, baseEnd_4374236] using wordTrace_append hprefix tailTrace_4374236
  have hstable : (prefixWord ++ tailWord_4374236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4374236).length < 2 ^ (prefixWord ++ tailWord_4374236).sum := by decide
  have hdescent : baseEnd_4374236 < baseStart_4374236 := by decide
  rcases family_descends (prefixWord ++ tailWord_4374236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4374352 : List Nat := [2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 4]
def baseStart_4374352 : Nat := 118140960795 + 4374352 * 2 ^ 59
def prefixEnd_4374352 : Nat := 4983230072969 + 3 ^ 40 * 4374352 * 2
def baseEnd_4374352 : Nat := 2246145127956374561382727

theorem tailTrace_4374352 : CollatzResearch.WordTrace tailWord_4374352 prefixEnd_4374352 2246145127956374561382727 := by
  unfold tailWord_4374352
  simp only [CollatzResearch.WordTrace]
  refine ⟨79772862324238629344322655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106363816432318172459096873 79772862324238629344322655)
  ·
    refine ⟨119659293486357944016483983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79772862324238629344322655 119659293486357944016483983)
    ·
      refine ⟨179488940229536916024725975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119659293486357944016483983 179488940229536916024725975)
      ·
        refine ⟨269233410344305374037088963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179488940229536916024725975 269233410344305374037088963)
        ·
          refine ⟨403850115516458061055633445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 269233410344305374037088963 403850115516458061055633445)
          ·
            refine ⟨75721896659335886447931271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 403850115516458061055633445 75721896659335886447931271)
            ·
              refine ⟨113582844989003829671896907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75721896659335886447931271 113582844989003829671896907)
              ·
                refine ⟨170374267483505744507845361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113582844989003829671896907 170374267483505744507845361)
                ·
                  refine ⟨127780700612629308380884021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 170374267483505744507845361 127780700612629308380884021)
                  ·
                    refine ⟨11979440682433997660707877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 127780700612629308380884021 11979440682433997660707877)
                    ·
                      refine ⟨2246145127956374561382727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11979440682433997660707877 2246145127956374561382727)
                      ·
                        rfl

theorem cell23_4374352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 4].length) (baseStart_4374352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4374352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4374352 prefixEnd_4374352 := by exact prefixLift 4374352
  have htrace : WordTrace (prefixWord ++ tailWord_4374352) baseStart_4374352 baseEnd_4374352 := by
    simpa [prefixWord, tailWord_4374352, baseEnd_4374352] using wordTrace_append hprefix tailTrace_4374352
  have hstable : (prefixWord ++ tailWord_4374352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4374352).length < 2 ^ (prefixWord ++ tailWord_4374352).sum := by decide
  have hdescent : baseEnd_4374352 < baseStart_4374352 := by decide
  rcases family_descends (prefixWord ++ tailWord_4374352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4374369 : List Nat := [1, 2, 3, 1, 1, 1, 5, 1, 3, 1, 4]
def baseStart_4374369 : Nat := 118140960795 + 4374369 * 2 ^ 59
def prefixEnd_4374369 : Nat := 4983230072969 + 3 ^ 40 * 4374369 * 2
def baseEnd_4374369 : Nat := 2246153857127500994870149

theorem tailTrace_4374369 : CollatzResearch.WordTrace tailWord_4374369 prefixEnd_4374369 2246153857127500994870149 := by
  unfold tailWord_4374369
  simp only [CollatzResearch.WordTrace]
  refine ⟨159546344689415670592014161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106364229792943780394676107 159546344689415670592014161)
  ·
    refine ⟨119659758517061752944010621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159546344689415670592014161 119659758517061752944010621)
    ·
      refine ⟨44872409443898157354003983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119659758517061752944010621 44872409443898157354003983)
      ·
        refine ⟨67308614165847236031005975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44872409443898157354003983 67308614165847236031005975)
        ·
          refine ⟨100962921248770854046508963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67308614165847236031005975 100962921248770854046508963)
          ·
            refine ⟨151444381873156281069763445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100962921248770854046508963 151444381873156281069763445)
            ·
              refine ⟨14197910800608401350290323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 151444381873156281069763445 14197910800608401350290323)
              ·
                refine ⟨21296866200912602025435485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14197910800608401350290323 21296866200912602025435485)
                ·
                  refine ⟨7986324825342225759538307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21296866200912602025435485 7986324825342225759538307)
                  ·
                    refine ⟨11979487238013338639307461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7986324825342225759538307 11979487238013338639307461)
                    ·
                      refine ⟨2246153857127500994870149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11979487238013338639307461 2246153857127500994870149)
                      ·
                        rfl

theorem cell23_4374369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 3, 1, 4].length) (baseStart_4374369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4374369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4374369 prefixEnd_4374369 := by exact prefixLift 4374369
  have htrace : WordTrace (prefixWord ++ tailWord_4374369) baseStart_4374369 baseEnd_4374369 := by
    simpa [prefixWord, tailWord_4374369, baseEnd_4374369] using wordTrace_append hprefix tailTrace_4374369
  have hstable : (prefixWord ++ tailWord_4374369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4374369).length < 2 ^ (prefixWord ++ tailWord_4374369).sum := by decide
  have hdescent : baseEnd_4374369 < baseStart_4374369 := by decide
  rcases family_descends (prefixWord ++ tailWord_4374369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4374420 : List Nat := [2, 4, 2, 1, 1, 3, 1, 2, 3, 2, 2]
def baseStart_4374420 : Nat := 118140960795 + 4374420 * 2 ^ 59
def prefixEnd_4374420 : Nat := 4983230072969 + 3 ^ 40 * 4374420 * 2
def baseEnd_4374420 : Nat := 2246180044640880295332415

theorem tailTrace_4374420 : CollatzResearch.WordTrace tailWord_4374420 prefixEnd_4374420 2246180044640880295332415 := by
  unfold tailWord_4374420
  simp only [CollatzResearch.WordTrace]
  refine ⟨79774102406115453151060357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106365469874820604201413809 79774102406115453151060357)
  ·
    refine ⟨14957644201146647465823817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79774102406115453151060357 14957644201146647465823817)
    ·
      refine ⟨11218233150859985599367863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14957644201146647465823817 11218233150859985599367863)
      ·
        refine ⟨16827349726289978399051795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11218233150859985599367863 16827349726289978399051795)
        ·
          refine ⟨25241024589434967598577693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16827349726289978399051795 25241024589434967598577693)
          ·
            refine ⟨9465384221038112849466635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25241024589434967598577693 9465384221038112849466635)
            ·
              refine ⟨14198076331557169274199953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9465384221038112849466635 14198076331557169274199953)
              ·
                refine ⟨10648557248667876955649965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14198076331557169274199953 10648557248667876955649965)
                ·
                  refine ⟨3993208968250453858368737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10648557248667876955649965 3993208968250453858368737)
                  ·
                    refine ⟨2994906726187840393776553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3993208968250453858368737 2994906726187840393776553)
                    ·
                      refine ⟨2246180044640880295332415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2994906726187840393776553 2246180044640880295332415)
                      ·
                        rfl

theorem cell23_4374420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 2, 3, 2, 2].length) (baseStart_4374420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4374420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4374420 prefixEnd_4374420 := by exact prefixLift 4374420
  have htrace : WordTrace (prefixWord ++ tailWord_4374420) baseStart_4374420 baseEnd_4374420 := by
    simpa [prefixWord, tailWord_4374420, baseEnd_4374420] using wordTrace_append hprefix tailTrace_4374420
  have hstable : (prefixWord ++ tailWord_4374420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4374420).length < 2 ^ (prefixWord ++ tailWord_4374420).sum := by decide
  have hdescent : baseEnd_4374420 < baseStart_4374420 := by decide
  rcases family_descends (prefixWord ++ tailWord_4374420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4374426 : List Nat := [3, 1, 1, 4, 2, 2, 3, 7]
def baseStart_4374426 : Nat := 118140960795 + 4374426 * 2 ^ 59
def prefixEnd_4374426 : Nat := 4983230072969 + 3 ^ 40 * 4374426 * 2
def baseEnd_4374426 : Nat := 83191967612029898957681

theorem tailTrace_4374426 : CollatzResearch.WordTrace tailWord_4374426 prefixEnd_4374426 83191967612029898957681 := by
  unfold tailWord_4374426
  simp only [CollatzResearch.WordTrace]
  refine ⟨39887105912552292331709783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106365615766806112884559421 39887105912552292331709783)
  ·
    refine ⟨59830658868828438497564675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39887105912552292331709783 59830658868828438497564675)
    ·
      refine ⟨89745988303242657746347013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59830658868828438497564675 89745988303242657746347013)
      ·
        refine ⟨16827372806857998327440065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 89745988303242657746347013 16827372806857998327440065)
        ·
          refine ⟨12620529605143498745580049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16827372806857998327440065 12620529605143498745580049)
          ·
            refine ⟨9465397203857624059185037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12620529605143498745580049 9465397203857624059185037)
            ·
              refine ⟨3549523951446609022194389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9465397203857624059185037 3549523951446609022194389)
              ·
                refine ⟨83191967612029898957681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3549523951446609022194389 83191967612029898957681)
                ·
                  rfl

theorem cell23_4374426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 3, 7].length) (baseStart_4374426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4374426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4374426 prefixEnd_4374426 := by exact prefixLift 4374426
  have htrace : WordTrace (prefixWord ++ tailWord_4374426) baseStart_4374426 baseEnd_4374426 := by
    simpa [prefixWord, tailWord_4374426, baseEnd_4374426] using wordTrace_append hprefix tailTrace_4374426
  have hstable : (prefixWord ++ tailWord_4374426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4374426).length < 2 ^ (prefixWord ++ tailWord_4374426).sum := by decide
  have hdescent : baseEnd_4374426 < baseStart_4374426 := by decide
  rcases family_descends (prefixWord ++ tailWord_4374426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4374436 : List Nat := [2, 3, 1, 2, 1, 3, 2, 2, 1, 3, 3]
def baseStart_4374436 : Nat := 118140960795 + 4374436 * 2 ^ 59
def prefixEnd_4374436 : Nat := 4983230072969 + 3 ^ 40 * 4374436 * 2
def baseEnd_4374436 : Nat := 2246188260331352232732341

theorem tailTrace_4374436 : CollatzResearch.WordTrace tailWord_4374436 prefixEnd_4374436 2246188260331352232732341 := by
  unfold tailWord_4374436
  simp only [CollatzResearch.WordTrace]
  refine ⟨79774394190086470517351581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106365858920115294023135441 79774394190086470517351581)
  ·
    refine ⟨29915397821282426444006843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79774394190086470517351581 29915397821282426444006843)
    ·
      refine ⟨44873096731923639666010265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29915397821282426444006843 44873096731923639666010265)
      ·
        refine ⟨33654822548942729749507699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44873096731923639666010265 33654822548942729749507699)
        ·
          refine ⟨50482233823414094624261549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33654822548942729749507699 50482233823414094624261549)
          ·
            refine ⟨18930837683780285484098081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50482233823414094624261549 18930837683780285484098081)
            ·
              refine ⟨14198128262835214113073561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18930837683780285484098081 14198128262835214113073561)
              ·
                refine ⟨10648596197126410584805171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14198128262835214113073561 10648596197126410584805171)
                ·
                  refine ⟨15972894295689615877207757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10648596197126410584805171 15972894295689615877207757)
                  ·
                    refine ⟨5989835360883605953952909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15972894295689615877207757 5989835360883605953952909)
                    ·
                      refine ⟨2246188260331352232732341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5989835360883605953952909 2246188260331352232732341)
                      ·
                        rfl

theorem cell23_4374436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 2, 1, 3, 3].length) (baseStart_4374436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4374436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4374436 prefixEnd_4374436 := by exact prefixLift 4374436
  have htrace : WordTrace (prefixWord ++ tailWord_4374436) baseStart_4374436 baseEnd_4374436 := by
    simpa [prefixWord, tailWord_4374436, baseEnd_4374436] using wordTrace_append hprefix tailTrace_4374436
  have hstable : (prefixWord ++ tailWord_4374436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4374436).length < 2 ^ (prefixWord ++ tailWord_4374436).sum := by decide
  have hdescent : baseEnd_4374436 < baseStart_4374436 := by decide
  rcases family_descends (prefixWord ++ tailWord_4374436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4374453 : List Nat := [1, 3, 3, 2, 1, 3, 1, 1, 4, 1, 3]
def baseStart_4374453 : Nat := 118140960795 + 4374453 * 2 ^ 59
def prefixEnd_4374453 : Nat := 4983230072969 + 3 ^ 40 * 4374453 * 2
def baseEnd_4374453 : Nat := 2246196989502478666219763

theorem tailTrace_4374453 : CollatzResearch.WordTrace tailWord_4374453 prefixEnd_4374453 2246196989502478666219763 := by
  unfold tailWord_4374453
  simp only [CollatzResearch.WordTrace]
  refine ⟨159549408421111352938072013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106366272280740901958714675 159549408421111352938072013)
  ·
    refine ⟨59831028157916757351777005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159549408421111352938072013 59831028157916757351777005)
    ·
      refine ⟨22436635559218784006916377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59831028157916757351777005 22436635559218784006916377)
      ·
        refine ⟨16827476669414088005187283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22436635559218784006916377 16827476669414088005187283)
        ·
          refine ⟨25241215004121132007780925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16827476669414088005187283 25241215004121132007780925)
          ·
            refine ⟨9465455626545424502917847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25241215004121132007780925 9465455626545424502917847)
            ·
              refine ⟨14198183439818136754376771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9465455626545424502917847 14198183439818136754376771)
              ·
                refine ⟨21297275159727205131565157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14198183439818136754376771 21297275159727205131565157)
                ·
                  refine ⟨3993239092448850962168467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21297275159727205131565157 3993239092448850962168467)
                  ·
                    refine ⟨5989858638673276443252701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3993239092448850962168467 5989858638673276443252701)
                    ·
                      refine ⟨2246196989502478666219763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5989858638673276443252701 2246196989502478666219763)
                      ·
                        rfl

theorem cell23_4374453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_4374453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4374453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4374453 prefixEnd_4374453 := by exact prefixLift 4374453
  have htrace : WordTrace (prefixWord ++ tailWord_4374453) baseStart_4374453 baseEnd_4374453 := by
    simpa [prefixWord, tailWord_4374453, baseEnd_4374453] using wordTrace_append hprefix tailTrace_4374453
  have hstable : (prefixWord ++ tailWord_4374453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4374453).length < 2 ^ (prefixWord ++ tailWord_4374453).sum := by decide
  have hdescent : baseEnd_4374453 < baseStart_4374453 := by decide
  rcases family_descends (prefixWord ++ tailWord_4374453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4374479 : List Nat := [1, 1, 2, 1, 1, 5, 2, 2, 2, 1, 5]
def baseStart_4374479 : Nat := 118140960795 + 4374479 * 2 ^ 59
def prefixEnd_4374479 : Nat := 4983230072969 + 3 ^ 40 * 4374479 * 2
def baseEnd_4374479 : Nat := 2246210339999495564494643

theorem tailTrace_4374479 : CollatzResearch.WordTrace tailWord_4374479 prefixEnd_4374479 2246210339999495564494643 := by
  unfold tailWord_4374479
  simp only [CollatzResearch.WordTrace]
  refine ⟨159550356719017159378518491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106366904479344772919012327 159550356719017159378518491)
  ·
    refine ⟨239325535078525739067777737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159550356719017159378518491 239325535078525739067777737)
    ·
      refine ⟨179494151308894304300833303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 239325535078525739067777737 179494151308894304300833303)
      ·
        refine ⟨269241226963341456451249955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179494151308894304300833303 269241226963341456451249955)
        ·
          refine ⟨403861840445012184676874933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 269241226963341456451249955 403861840445012184676874933)
          ·
            refine ⟨37862047541719892313457025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 403861840445012184676874933 37862047541719892313457025)
            ·
              refine ⟨28396535656289919235092769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37862047541719892313457025 28396535656289919235092769)
              ·
                refine ⟨21297401742217439426319577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28396535656289919235092769 21297401742217439426319577)
                ·
                  refine ⟨15973051306663079569739683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21297401742217439426319577 15973051306663079569739683)
                  ·
                    refine ⟨23959576959994619354609525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15973051306663079569739683 23959576959994619354609525)
                    ·
                      refine ⟨2246210339999495564494643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23959576959994619354609525 2246210339999495564494643)
                      ·
                        rfl

theorem cell23_4374479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 2, 2, 1, 5].length) (baseStart_4374479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4374479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4374479 prefixEnd_4374479 := by exact prefixLift 4374479
  have htrace : WordTrace (prefixWord ++ tailWord_4374479) baseStart_4374479 baseEnd_4374479 := by
    simpa [prefixWord, tailWord_4374479, baseEnd_4374479] using wordTrace_append hprefix tailTrace_4374479
  have hstable : (prefixWord ++ tailWord_4374479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4374479).length < 2 ^ (prefixWord ++ tailWord_4374479).sum := by decide
  have hdescent : baseEnd_4374479 < baseStart_4374479 := by decide
  rcases family_descends (prefixWord ++ tailWord_4374479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4374510 : List Nat := [4, 1, 2, 1, 3, 1, 2, 1, 4, 2, 2]
def baseStart_4374510 : Nat := 118140960795 + 4374510 * 2 ^ 59
def prefixEnd_4374510 : Nat := 4983230072969 + 3 ^ 40 * 4374510 * 2
def baseEnd_4374510 : Nat := 2246226257899784943207001

theorem tailTrace_4374510 : CollatzResearch.WordTrace tailWord_4374510 prefixEnd_4374510 2246226257899784943207001 := by
  unfold tailWord_4374510
  simp only [CollatzResearch.WordTrace]
  refine ⟨19943935922738106459112123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106367658254603234448597989 19943935922738106459112123)
  ·
    refine ⟨29915903884107159688668185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19943935922738106459112123 29915903884107159688668185)
    ·
      refine ⟨22436927913080369766501139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29915903884107159688668185 22436927913080369766501139)
      ·
        refine ⟨33655391869620554649751709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22436927913080369766501139 33655391869620554649751709)
        ·
          refine ⟨12620771951107707993656891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33655391869620554649751709 12620771951107707993656891)
          ·
            refine ⟨18931157926661561990485337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12620771951107707993656891 18931157926661561990485337)
            ·
              refine ⟨14198368444996171492864003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18931157926661561990485337 14198368444996171492864003)
              ·
                refine ⟨21297552667494257239296005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14198368444996171492864003 21297552667494257239296005)
                ·
                  refine ⟨3993291125155173232368001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21297552667494257239296005 3993291125155173232368001)
                  ·
                    refine ⟨2994968343866379924276001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3993291125155173232368001 2994968343866379924276001)
                    ·
                      refine ⟨2246226257899784943207001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2994968343866379924276001 2246226257899784943207001)
                      ·
                        rfl

theorem cell23_4374510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 4, 2, 2].length) (baseStart_4374510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4374510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4374510 prefixEnd_4374510 := by exact prefixLift 4374510
  have htrace : WordTrace (prefixWord ++ tailWord_4374510) baseStart_4374510 baseEnd_4374510 := by
    simpa [prefixWord, tailWord_4374510, baseEnd_4374510] using wordTrace_append hprefix tailTrace_4374510
  have hstable : (prefixWord ++ tailWord_4374510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4374510).length < 2 ^ (prefixWord ++ tailWord_4374510).sum := by decide
  have hdescent : baseEnd_4374510 < baseStart_4374510 := by decide
  rcases family_descends (prefixWord ++ tailWord_4374510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4374539 : List Nat := [1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 7]
def baseStart_4374539 : Nat := 118140960795 + 4374539 * 2 ^ 59
def prefixEnd_4374539 : Nat := 4983230072969 + 3 ^ 40 * 4374539 * 2
def baseEnd_4374539 : Nat := 2246241148838765329744367

theorem tailTrace_4374539 : CollatzResearch.WordTrace tailWord_4374539 prefixEnd_4374539 2246241148838765329744367 := by
  unfold tailWord_4374539
  simp only [CollatzResearch.WordTrace]
  refine ⟨159552545098799789625702671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106368363399199859750468447 159552545098799789625702671)
  ·
    refine ⟨239328817648199684438554007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159552545098799789625702671 239328817648199684438554007)
    ·
      refine ⟨358993226472299526657831011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239328817648199684438554007 358993226472299526657831011)
      ·
        refine ⟨538489839708449289986746517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 358993226472299526657831011 538489839708449289986746517)
        ·
          refine ⟨25241711236333560468128743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 538489839708449289986746517 25241711236333560468128743)
          ·
            refine ⟨37862566854500340702193115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25241711236333560468128743 37862566854500340702193115)
            ·
              refine ⟨56793850281750511053289673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37862566854500340702193115 56793850281750511053289673)
              ·
                refine ⟨42595387711312883289967255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56793850281750511053289673 42595387711312883289967255)
                ·
                  refine ⟨63893081566969324934950883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42595387711312883289967255 63893081566969324934950883)
                  ·
                    refine ⟨95839622350453987402426325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 63893081566969324934950883 95839622350453987402426325)
                    ·
                      refine ⟨2246241148838765329744367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 95839622350453987402426325 2246241148838765329744367)
                      ·
                        rfl

theorem cell23_4374539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 7].length) (baseStart_4374539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4374539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4374539 prefixEnd_4374539 := by exact prefixLift 4374539
  have htrace : WordTrace (prefixWord ++ tailWord_4374539) baseStart_4374539 baseEnd_4374539 := by
    simpa [prefixWord, tailWord_4374539, baseEnd_4374539] using wordTrace_append hprefix tailTrace_4374539
  have hstable : (prefixWord ++ tailWord_4374539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4374539).length < 2 ^ (prefixWord ++ tailWord_4374539).sum := by decide
  have hdescent : baseEnd_4374539 < baseStart_4374539 := by decide
  rcases family_descends (prefixWord ++ tailWord_4374539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4374556 : List Nat := [2, 2, 3, 1, 3, 1, 1, 2, 1, 2, 5]
def baseStart_4374556 : Nat := 118140960795 + 4374556 * 2 ^ 59
def prefixEnd_4374556 : Nat := 4983230072969 + 3 ^ 40 * 4374556 * 2
def baseEnd_4374556 : Nat := 2246249878009891763231789

theorem tailTrace_4374556 : CollatzResearch.WordTrace tailWord_4374556 prefixEnd_4374556 2246249878009891763231789 := by
  unfold tailWord_4374556
  simp only [CollatzResearch.WordTrace]
  refine ⟨79776582569869100764535761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106368776759825467686047681 79776582569869100764535761)
  ·
    refine ⟨59832436927401825573401821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79776582569869100764535761 59832436927401825573401821)
    ·
      refine ⟨22437163847775684590025683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59832436927401825573401821 22437163847775684590025683)
      ·
        refine ⟨33655745771663526885038525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22437163847775684590025683 33655745771663526885038525)
        ·
          refine ⟨12620904664373822581889447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33655745771663526885038525 12620904664373822581889447)
          ·
            refine ⟨18931356996560733872834171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12620904664373822581889447 18931356996560733872834171)
            ·
              refine ⟨28397035494841100809251257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18931356996560733872834171 28397035494841100809251257)
              ·
                refine ⟨21297776621130825606938443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28397035494841100809251257 21297776621130825606938443)
                ·
                  refine ⟨31946664931696238410407665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21297776621130825606938443 31946664931696238410407665)
                  ·
                    refine ⟨23959998698772178807805749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31946664931696238410407665 23959998698772178807805749)
                    ·
                      refine ⟨2246249878009891763231789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23959998698772178807805749 2246249878009891763231789)
                      ·
                        rfl

theorem cell23_4374556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_4374556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4374556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4374556 prefixEnd_4374556 := by exact prefixLift 4374556
  have htrace : WordTrace (prefixWord ++ tailWord_4374556) baseStart_4374556 baseEnd_4374556 := by
    simpa [prefixWord, tailWord_4374556, baseEnd_4374556] using wordTrace_append hprefix tailTrace_4374556
  have hstable : (prefixWord ++ tailWord_4374556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4374556).length < 2 ^ (prefixWord ++ tailWord_4374556).sum := by decide
  have hdescent : baseEnd_4374556 < baseStart_4374556 := by decide
  rcases family_descends (prefixWord ++ tailWord_4374556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4374586 : List Nat := [3, 1, 1, 1, 3, 1, 1, 4, 1, 4, 3]
def baseStart_4374586 : Nat := 118140960795 + 4374586 * 2 ^ 59
def prefixEnd_4374586 : Nat := 4983230072969 + 3 ^ 40 * 4374586 * 2
def baseEnd_4374586 : Nat := 2246265282429526645856651

theorem tailTrace_4374586 : CollatzResearch.WordTrace tailWord_4374586 prefixEnd_4374586 2246265282429526645856651 := by
  unfold tailWord_4374586
  simp only [CollatzResearch.WordTrace]
  refine ⟨39888564832407379163165903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106369506219753011101775741 39888564832407379163165903)
  ·
    refine ⟨59832847248611068744748855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39888564832407379163165903 59832847248611068744748855)
    ·
      refine ⟨89749270872916603117123283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59832847248611068744748855 89749270872916603117123283)
      ·
        refine ⟨134623906309374904675684925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89749270872916603117123283 134623906309374904675684925)
        ·
          refine ⟨50483964866015589253381847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134623906309374904675684925 50483964866015589253381847)
          ·
            refine ⟨75725947299023383880072771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50483964866015589253381847 75725947299023383880072771)
            ·
              refine ⟨113588920948535075820109157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75725947299023383880072771 113588920948535075820109157)
              ·
                refine ⟨21297922677850326716270467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 113588920948535075820109157 21297922677850326716270467)
                ·
                  refine ⟨31946884016775490074405701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21297922677850326716270467 31946884016775490074405701)
                  ·
                    refine ⟨5990040753145404388951069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31946884016775490074405701 5990040753145404388951069)
                    ·
                      refine ⟨2246265282429526645856651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5990040753145404388951069 2246265282429526645856651)
                      ·
                        rfl

theorem cell23_4374586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 1, 4, 3].length) (baseStart_4374586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4374586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4374586 prefixEnd_4374586 := by exact prefixLift 4374586
  have htrace : WordTrace (prefixWord ++ tailWord_4374586) baseStart_4374586 baseEnd_4374586 := by
    simpa [prefixWord, tailWord_4374586, baseEnd_4374586] using wordTrace_append hprefix tailTrace_4374586
  have hstable : (prefixWord ++ tailWord_4374586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4374586).length < 2 ^ (prefixWord ++ tailWord_4374586).sum := by decide
  have hdescent : baseEnd_4374586 < baseStart_4374586 := by decide
  rcases family_descends (prefixWord ++ tailWord_4374586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4374593 : List Nat := [1, 2, 5, 1, 2, 1, 1, 1, 5, 4]
def baseStart_4374593 : Nat := 118140960795 + 4374593 * 2 ^ 59
def prefixEnd_4374593 : Nat := 4983230072969 + 3 ^ 40 * 4374593 * 2
def baseEnd_4374593 : Nat := 748756292264702706156373

theorem tailTrace_4374593 : CollatzResearch.WordTrace tailWord_4374593 prefixEnd_4374593 748756292264702706156373 := by
  unfold tailWord_4374593
  simp only [CollatzResearch.WordTrace]
  refine ⟨159554514640604156848168433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106369676427069437898778955 159554514640604156848168433)
  ·
    refine ⟨119665885980453117636126325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159554514640604156848168433 119665885980453117636126325)
    ·
      refine ⟨11218676810667479778386843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 119665885980453117636126325 11218676810667479778386843)
      ·
        refine ⟨16828015216001219667580265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11218676810667479778386843 16828015216001219667580265)
        ·
          refine ⟨12621011412000914750685199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16828015216001219667580265 12621011412000914750685199)
          ·
            refine ⟨18931517118001372126027799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12621011412000914750685199 18931517118001372126027799)
            ·
              refine ⟨28397275677002058189041699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18931517118001372126027799 28397275677002058189041699)
              ·
                refine ⟨42595913515503087283562549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28397275677002058189041699 42595913515503087283562549)
                ·
                  refine ⟨3993366892078414432833989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42595913515503087283562549 3993366892078414432833989)
                  ·
                    refine ⟨748756292264702706156373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3993366892078414432833989 748756292264702706156373)
                    ·
                      rfl

theorem cell23_4374593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_4374593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4374593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4374593 prefixEnd_4374593 := by exact prefixLift 4374593
  have htrace : WordTrace (prefixWord ++ tailWord_4374593) baseStart_4374593 baseEnd_4374593 := by
    simpa [prefixWord, tailWord_4374593, baseEnd_4374593] using wordTrace_append hprefix tailTrace_4374593
  have hstable : (prefixWord ++ tailWord_4374593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4374593).length < 2 ^ (prefixWord ++ tailWord_4374593).sum := by decide
  have hdescent : baseEnd_4374593 < baseStart_4374593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4374593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4374653 : List Nat := [1, 4, 1, 1, 3, 2, 1, 4, 1, 5]
def baseStart_4374653 : Nat := 118140960795 + 4374653 * 2 ^ 59
def prefixEnd_4374653 : Nat := 4983230072969 + 3 ^ 40 * 4374653 * 2
def baseEnd_4374653 : Nat := 748766561877792627906281

theorem tailTrace_4374653 : CollatzResearch.WordTrace tailWord_4374653 prefixEnd_4374653 748766561877792627906281 := by
  unfold tailWord_4374653
  simp only [CollatzResearch.WordTrace]
  refine ⟨159556703020386787095352613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106371135346924524730235075 159556703020386787095352613)
  ·
    refine ⟨29916881816322522580378615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 159556703020386787095352613 29916881816322522580378615)
    ·
      refine ⟨44875322724483783870567923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29916881816322522580378615 44875322724483783870567923)
      ·
        refine ⟨67312984086725675805851885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44875322724483783870567923 67312984086725675805851885)
        ·
          refine ⟨25242369032522128427194457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67312984086725675805851885 25242369032522128427194457)
          ·
            refine ⟨18931776774391596320395843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25242369032522128427194457 18931776774391596320395843)
            ·
              refine ⟨28397665161587394480593765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18931776774391596320395843 28397665161587394480593765)
              ·
                refine ⟨5324562217797636465111331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28397665161587394480593765 5324562217797636465111331)
                ·
                  refine ⟨7986843326696454697666997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5324562217797636465111331 7986843326696454697666997)
                  ·
                    refine ⟨748766561877792627906281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7986843326696454697666997 748766561877792627906281)
                    ·
                      rfl

theorem cell23_4374653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 4, 1, 5].length) (baseStart_4374653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4374653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4374653 prefixEnd_4374653 := by exact prefixLift 4374653
  have htrace : WordTrace (prefixWord ++ tailWord_4374653) baseStart_4374653 baseEnd_4374653 := by
    simpa [prefixWord, tailWord_4374653, baseEnd_4374653] using wordTrace_append hprefix tailTrace_4374653
  have hstable : (prefixWord ++ tailWord_4374653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4374653).length < 2 ^ (prefixWord ++ tailWord_4374653).sum := by decide
  have hdescent : baseEnd_4374653 < baseStart_4374653 := by decide
  rcases family_descends (prefixWord ++ tailWord_4374653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4374660 : List Nat := [2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2]
def baseStart_4374660 : Nat := 118140960795 + 4374660 * 2 ^ 59
def prefixEnd_4374660 : Nat := 4983230072969 + 3 ^ 40 * 4374660 * 2
def baseEnd_4374660 : Nat := 2246303279997959356331311

theorem tailTrace_4374660 : CollatzResearch.WordTrace tailWord_4374660 prefixEnd_4374660 2246303279997959356331311 := by
  unfold tailWord_4374660
  simp only [CollatzResearch.WordTrace]
  refine ⟨79778479165680713645428717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106371305554240951527238289 79778479165680713645428717)
  ·
    refine ⟨29916929687130267617035769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79778479165680713645428717 29916929687130267617035769)
    ·
      refine ⟨22437697265347700712776827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29916929687130267617035769 22437697265347700712776827)
      ·
        refine ⟨33656545898021551069165241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22437697265347700712776827 33656545898021551069165241)
        ·
          refine ⟨25242409423516163301873931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33656545898021551069165241 25242409423516163301873931)
          ·
            refine ⟨37863614135274244952810897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25242409423516163301873931 37863614135274244952810897)
            ·
              refine ⟨28397710601455683714608173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37863614135274244952810897 28397710601455683714608173)
              ·
                refine ⟨10649141475545881392978065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28397710601455683714608173 10649141475545881392978065)
                ·
                  refine ⟨7986856106659411044733549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10649141475545881392978065 7986856106659411044733549)
                  ·
                    refine ⟨2995071039997279141775081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7986856106659411044733549 2995071039997279141775081)
                    ·
                      refine ⟨2246303279997959356331311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2995071039997279141775081 2246303279997959356331311)
                      ·
                        rfl

theorem cell23_4374660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2].length) (baseStart_4374660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4374660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4374660 prefixEnd_4374660 := by exact prefixLift 4374660
  have htrace : WordTrace (prefixWord ++ tailWord_4374660) baseStart_4374660 baseEnd_4374660 := by
    simpa [prefixWord, tailWord_4374660, baseEnd_4374660] using wordTrace_append hprefix tailTrace_4374660
  have hstable : (prefixWord ++ tailWord_4374660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4374660).length < 2 ^ (prefixWord ++ tailWord_4374660).sum := by decide
  have hdescent : baseEnd_4374660 < baseStart_4374660 := by decide
  rcases family_descends (prefixWord ++ tailWord_4374660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4374678 : List Nat := [5, 3, 2, 1, 1, 2, 1, 1, 3, 4]
def baseStart_4374678 : Nat := 118140960795 + 4374678 * 2 ^ 59
def prefixEnd_4374678 : Nat := 4983230072969 + 3 ^ 40 * 4374678 * 2
def baseEnd_4374678 : Nat := 748770840883246761968743

theorem tailTrace_4374678 : CollatzResearch.WordTrace tailWord_4374678 prefixEnd_4374678 748770840883246761968743 := by
  unfold tailWord_4374678
  simp only [CollatzResearch.WordTrace]
  refine ⟨9972350927831013522813293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 106371743230197477576675125 9972350927831013522813293)
  ·
    refine ⟨3739631597936630071054985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9972350927831013522813293 3739631597936630071054985)
    ·
      refine ⟨2804723698452472553291239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3739631597936630071054985 2804723698452472553291239)
      ·
        refine ⟨4207085547678708829936859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2804723698452472553291239 4207085547678708829936859)
        ·
          refine ⟨6310628321518063244905289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4207085547678708829936859 6310628321518063244905289)
          ·
            refine ⟨4732971241138547433678967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6310628321518063244905289 4732971241138547433678967)
            ·
              refine ⟨7099456861707821150518451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4732971241138547433678967 7099456861707821150518451)
              ·
                refine ⟨10649185292561731725777677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7099456861707821150518451 10649185292561731725777677)
                ·
                  refine ⟨3993444484710649397166629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10649185292561731725777677 3993444484710649397166629)
                  ·
                    refine ⟨748770840883246761968743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3993444484710649397166629 748770840883246761968743)
                    ·
                      rfl

theorem cell23_4374678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_4374678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4374678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4374678 prefixEnd_4374678 := by exact prefixLift 4374678
  have htrace : WordTrace (prefixWord ++ tailWord_4374678) baseStart_4374678 baseEnd_4374678 := by
    simpa [prefixWord, tailWord_4374678, baseEnd_4374678] using wordTrace_append hprefix tailTrace_4374678
  have hstable : (prefixWord ++ tailWord_4374678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4374678).length < 2 ^ (prefixWord ++ tailWord_4374678).sum := by decide
  have hdescent : baseEnd_4374678 < baseStart_4374678 := by decide
  rcases family_descends (prefixWord ++ tailWord_4374678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4374684 : List Nat := [2, 2, 3, 2, 1, 1, 5, 2, 1, 1, 3]
def baseStart_4374684 : Nat := 118140960795 + 4374684 * 2 ^ 59
def prefixEnd_4374684 : Nat := 4983230072969 + 3 ^ 40 * 4374684 * 2
def baseEnd_4374684 : Nat := 2246315603533667262431201

theorem tailTrace_4374684 : CollatzResearch.WordTrace tailWord_4374684 prefixEnd_4374684 2246315603533667262431201 := by
  unfold tailWord_4374684
  simp only [CollatzResearch.WordTrace]
  refine ⟨79778916841637239694865553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106371889122182986259820737 79778916841637239694865553)
  ·
    refine ⟨59834187631227929771149165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79778916841637239694865553 59834187631227929771149165)
    ·
      refine ⟨22437820361710473664180937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59834187631227929771149165 22437820361710473664180937)
      ·
        refine ⟨16828365271282855248135703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22437820361710473664180937 16828365271282855248135703)
        ·
          refine ⟨25242547906924282872203555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16828365271282855248135703 25242547906924282872203555)
          ·
            refine ⟨37863821860386424308305333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25242547906924282872203555 37863821860386424308305333)
            ·
              refine ⟨3549733299411227278903625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37863821860386424308305333 3549733299411227278903625)
              ·
                refine ⟨2662299974558420459177719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3549733299411227278903625 2662299974558420459177719)
                ·
                  refine ⟨3993449961837630688766579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2662299974558420459177719 3993449961837630688766579)
                  ·
                    refine ⟨5990174942756446033149869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3993449961837630688766579 5990174942756446033149869)
                    ·
                      refine ⟨2246315603533667262431201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5990174942756446033149869 2246315603533667262431201)
                      ·
                        rfl

theorem cell23_4374684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 5, 2, 1, 1, 3].length) (baseStart_4374684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4374684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4374684 prefixEnd_4374684 := by exact prefixLift 4374684
  have htrace : WordTrace (prefixWord ++ tailWord_4374684) baseStart_4374684 baseEnd_4374684 := by
    simpa [prefixWord, tailWord_4374684, baseEnd_4374684] using wordTrace_append hprefix tailTrace_4374684
  have hstable : (prefixWord ++ tailWord_4374684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4374684).length < 2 ^ (prefixWord ++ tailWord_4374684).sum := by decide
  have hdescent : baseEnd_4374684 < baseStart_4374684 := by decide
  rcases family_descends (prefixWord ++ tailWord_4374684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4374693 : List Nat := [1, 3, 1, 2, 1, 3, 2, 2, 3, 2, 3]
def baseStart_4374693 : Nat := 118140960795 + 4374693 * 2 ^ 59
def prefixEnd_4374693 : Nat := 4983230072969 + 3 ^ 40 * 4374693 * 2
def baseEnd_4374693 : Nat := 2246320224859557727218659

theorem tailTrace_4374693 : CollatzResearch.WordTrace tailWord_4374693 prefixEnd_4374693 2246320224859557727218659 := by
  unfold tailWord_4374693
  simp only [CollatzResearch.WordTrace]
  refine ⟨159558161940241873926808733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106372107960161249284539155 159558161940241873926808733)
  ·
    refine ⟨59834310727590702722553275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159558161940241873926808733 59834310727590702722553275)
    ·
      refine ⟨89751466091386054083829913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59834310727590702722553275 89751466091386054083829913)
      ·
        refine ⟨67313599568539540562872435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89751466091386054083829913 67313599568539540562872435)
        ·
          refine ⟨100970399352809310844308653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67313599568539540562872435 100970399352809310844308653)
          ·
            refine ⟨37863899757303491566615745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100970399352809310844308653 37863899757303491566615745)
            ·
              refine ⟨28397924817977618674961809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37863899757303491566615745 28397924817977618674961809)
              ·
                refine ⟨21298443613483214006221357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28397924817977618674961809 21298443613483214006221357)
                ·
                  refine ⟨7986916355056205252333009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21298443613483214006221357 7986916355056205252333009)
                  ·
                    refine ⟨5990187266292153939249757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7986916355056205252333009 5990187266292153939249757)
                    ·
                      refine ⟨2246320224859557727218659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5990187266292153939249757 2246320224859557727218659)
                      ·
                        rfl

theorem cell23_4374693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 3, 2, 3].length) (baseStart_4374693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4374693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4374693 prefixEnd_4374693 := by exact prefixLift 4374693
  have htrace : WordTrace (prefixWord ++ tailWord_4374693) baseStart_4374693 baseEnd_4374693 := by
    simpa [prefixWord, tailWord_4374693, baseEnd_4374693] using wordTrace_append hprefix tailTrace_4374693
  have hstable : (prefixWord ++ tailWord_4374693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4374693).length < 2 ^ (prefixWord ++ tailWord_4374693).sum := by decide
  have hdescent : baseEnd_4374693 < baseStart_4374693 := by decide
  rcases family_descends (prefixWord ++ tailWord_4374693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4374741 : List Nat := [1, 3, 2, 4, 2, 1, 1, 4, 1, 2, 2]
def baseStart_4374741 : Nat := 118140960795 + 4374741 * 2 ^ 59
def prefixEnd_4374741 : Nat := 4983230072969 + 3 ^ 40 * 4374741 * 2
def baseEnd_4374741 : Nat := 2246344871930973539418439

theorem tailTrace_4374741 : CollatzResearch.WordTrace tailWord_4374741 prefixEnd_4374741 2246344871930973539418439 := by
  unfold tailWord_4374741
  simp only [CollatzResearch.WordTrace]
  refine ⟨159559912644067978124556077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106373275096045318749704051 159559912644067978124556077)
  ·
    refine ⟨59834967241525491796708529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159559912644067978124556077 59834967241525491796708529)
    ·
      refine ⟨44876225431144118847531397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59834967241525491796708529 44876225431144118847531397)
      ·
        refine ⟨8414292268339522283912137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44876225431144118847531397 8414292268339522283912137)
        ·
          refine ⟨6310719201254641712934103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8414292268339522283912137 6310719201254641712934103)
          ·
            refine ⟨9466078801881962569401155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6310719201254641712934103 9466078801881962569401155)
            ·
              refine ⟨14199118202822943854101733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9466078801881962569401155 14199118202822943854101733)
              ·
                refine ⟨2662334663029301972644075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14199118202822943854101733 2662334663029301972644075)
                ·
                  refine ⟨3993501994543952958966113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2662334663029301972644075 3993501994543952958966113)
                  ·
                    refine ⟨2995126495907964719224585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3993501994543952958966113 2995126495907964719224585)
                    ·
                      refine ⟨2246344871930973539418439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2995126495907964719224585 2246344871930973539418439)
                      ·
                        rfl

theorem cell23_4374741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_4374741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4374741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4374741 prefixEnd_4374741 := by exact prefixLift 4374741
  have htrace : WordTrace (prefixWord ++ tailWord_4374741) baseStart_4374741 baseEnd_4374741 := by
    simpa [prefixWord, tailWord_4374741, baseEnd_4374741] using wordTrace_append hprefix tailTrace_4374741
  have hstable : (prefixWord ++ tailWord_4374741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4374741).length < 2 ^ (prefixWord ++ tailWord_4374741).sum := by decide
  have hdescent : baseEnd_4374741 < baseStart_4374741 := by decide
  rcases family_descends (prefixWord ++ tailWord_4374741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4374757 : List Nat := [1, 3, 1, 4, 2, 1, 2, 3, 2, 1, 3]
def baseStart_4374757 : Nat := 118140960795 + 4374757 * 2 ^ 59
def prefixEnd_4374757 : Nat := 4983230072969 + 3 ^ 40 * 4374757 * 2
def baseEnd_4374757 : Nat := 2246353087621445476818365

theorem tailTrace_4374757 : CollatzResearch.WordTrace tailWord_4374757 prefixEnd_4374757 2246353087621445476818365 := by
  unfold tailWord_4374757
  simp only [CollatzResearch.WordTrace]
  refine ⟨159560496212010012857138525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106373664141340008571425683 159560496212010012857138525)
  ·
    refine ⟨59835186079503754821426947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159560496212010012857138525 59835186079503754821426947)
    ·
      refine ⟨89752779119255632232140421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59835186079503754821426947 89752779119255632232140421)
      ·
        refine ⟨16828646084860431043526329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 89752779119255632232140421 16828646084860431043526329)
        ·
          refine ⟨12621484563645323282644747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16828646084860431043526329 12621484563645323282644747)
          ·
            refine ⟨18932226845467984923967121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12621484563645323282644747 18932226845467984923967121)
            ·
              refine ⟨14199170134100988692975341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18932226845467984923967121 14199170134100988692975341)
              ·
                refine ⟨5324688800287870759865753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14199170134100988692975341 5324688800287870759865753)
                ·
                  refine ⟨3993516600215903069899315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5324688800287870759865753 3993516600215903069899315)
                  ·
                    refine ⟨5990274900323854604848973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3993516600215903069899315 5990274900323854604848973)
                    ·
                      refine ⟨2246353087621445476818365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5990274900323854604848973 2246353087621445476818365)
                      ·
                        rfl

theorem cell23_4374757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_4374757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4374757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4374757 prefixEnd_4374757 := by exact prefixLift 4374757
  have htrace : WordTrace (prefixWord ++ tailWord_4374757) baseStart_4374757 baseEnd_4374757 := by
    simpa [prefixWord, tailWord_4374757, baseEnd_4374757] using wordTrace_append hprefix tailTrace_4374757
  have hstable : (prefixWord ++ tailWord_4374757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4374757).length < 2 ^ (prefixWord ++ tailWord_4374757).sum := by decide
  have hdescent : baseEnd_4374757 < baseStart_4374757 := by decide
  rcases family_descends (prefixWord ++ tailWord_4374757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4374791 : List Nat := [1, 1, 4, 5, 1, 2, 1, 2, 2, 1, 3]
def baseStart_4374791 : Nat := 118140960795 + 4374791 * 2 ^ 59
def prefixEnd_4374791 : Nat := 4983230072969 + 3 ^ 40 * 4374791 * 2
def baseEnd_4374791 : Nat := 2246370545963698343793209

theorem tailTrace_4374791 : CollatzResearch.WordTrace tailWord_4374791 prefixEnd_4374791 2246370545963698343793209 := by
  unfold tailWord_4374791
  simp only [CollatzResearch.WordTrace]
  refine ⟨159561736293886836663876227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106374490862591224442584151 159561736293886836663876227)
  ·
    refine ⟨239342604440830254995814341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159561736293886836663876227 239342604440830254995814341)
    ·
      refine ⟨44876738332655672811715189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 239342604440830254995814341 44876738332655672811715189)
      ·
        refine ⟨4207194218686469326098299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44876738332655672811715189 4207194218686469326098299)
        ·
          refine ⟨6310791328029703989147449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4207194218686469326098299 6310791328029703989147449)
          ·
            refine ⟨4733093496022277991860587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6310791328029703989147449 4733093496022277991860587)
            ·
              refine ⟨7099640244033416987790881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4733093496022277991860587 7099640244033416987790881)
              ·
                refine ⟨5324730183025062740843161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7099640244033416987790881 5324730183025062740843161)
                ·
                  refine ⟨3993547637268797055632371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5324730183025062740843161 3993547637268797055632371)
                  ·
                    refine ⟨5990321455903195583448557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3993547637268797055632371 5990321455903195583448557)
                    ·
                      refine ⟨2246370545963698343793209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5990321455903195583448557 2246370545963698343793209)
                      ·
                        rfl

theorem cell23_4374791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_4374791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4374791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4374791 prefixEnd_4374791 := by exact prefixLift 4374791
  have htrace : WordTrace (prefixWord ++ tailWord_4374791) baseStart_4374791 baseEnd_4374791 := by
    simpa [prefixWord, tailWord_4374791, baseEnd_4374791] using wordTrace_append hprefix tailTrace_4374791
  have hstable : (prefixWord ++ tailWord_4374791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4374791).length < 2 ^ (prefixWord ++ tailWord_4374791).sum := by decide
  have hdescent : baseEnd_4374791 < baseStart_4374791 := by decide
  rcases family_descends (prefixWord ++ tailWord_4374791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4374793 : List Nat := [1, 2, 1, 1, 3, 4, 1, 2, 2, 2, 4]
def baseStart_4374793 : Nat := 118140960795 + 4374793 * 2 ^ 59
def prefixEnd_4374793 : Nat := 4983230072969 + 3 ^ 40 * 4374793 * 2
def baseEnd_4374793 : Nat := 2246371572925007335968199

theorem tailTrace_4374793 : CollatzResearch.WordTrace tailWord_4374793 prefixEnd_4374793 2246371572925007335968199 := by
  unfold tailWord_4374793
  simp only [CollatzResearch.WordTrace]
  refine ⟨159561809239879591005449033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106374539493253060670299355 159561809239879591005449033)
  ·
    refine ⟨119671356929909693254086775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159561809239879591005449033 119671356929909693254086775)
    ·
      refine ⟨179507035394864539881130163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119671356929909693254086775 179507035394864539881130163)
      ·
        refine ⟨269260553092296809821695245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179507035394864539881130163 269260553092296809821695245)
        ·
          refine ⟨100972707409611303683135717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 269260553092296809821695245 100972707409611303683135717)
          ·
            refine ⟨18932382639302119440587947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 100972707409611303683135717 18932382639302119440587947)
            ·
              refine ⟨28398573958953179160881921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18932382639302119440587947 28398573958953179160881921)
              ·
                refine ⟨21298930469214884370661441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28398573958953179160881921 21298930469214884370661441)
                ·
                  refine ⟨15974197851911163277996081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21298930469214884370661441 15974197851911163277996081)
                  ·
                    refine ⟨11980648388933372458497061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15974197851911163277996081 11980648388933372458497061)
                    ·
                      refine ⟨2246371572925007335968199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11980648388933372458497061 2246371572925007335968199)
                      ·
                        rfl

theorem cell23_4374793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 2, 2, 4].length) (baseStart_4374793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4374793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4374793 prefixEnd_4374793 := by exact prefixLift 4374793
  have htrace : WordTrace (prefixWord ++ tailWord_4374793) baseStart_4374793 baseEnd_4374793 := by
    simpa [prefixWord, tailWord_4374793, baseEnd_4374793] using wordTrace_append hprefix tailTrace_4374793
  have hstable : (prefixWord ++ tailWord_4374793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4374793).length < 2 ^ (prefixWord ++ tailWord_4374793).sum := by decide
  have hdescent : baseEnd_4374793 < baseStart_4374793 := by decide
  rcases family_descends (prefixWord ++ tailWord_4374793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4374887 : List Nat := [1, 1, 5, 1, 3, 2, 2, 1, 2, 1, 4]
def baseStart_4374887 : Nat := 118140960795 + 4374887 * 2 ^ 59
def prefixEnd_4374887 : Nat := 4983230072969 + 3 ^ 40 * 4374887 * 2
def baseEnd_4374887 : Nat := 2246419840106529968192767

theorem tailTrace_4374887 : CollatzResearch.WordTrace tailWord_4374887 prefixEnd_4374887 2246419840106529968192767 := by
  unfold tailWord_4374887
  simp only [CollatzResearch.WordTrace]
  refine ⟨159565237701539045059370915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106376825134359363372913943 159565237701539045059370915)
  ·
    refine ⟨239347856552308567589056373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159565237701539045059370915 239347856552308567589056373)
    ·
      refine ⟨22438861551778928211474035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 239347856552308567589056373 22438861551778928211474035)
      ·
        refine ⟨33658292327668392317211053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22438861551778928211474035 33658292327668392317211053)
        ·
          refine ⟨12621859622875647118954145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33658292327668392317211053 12621859622875647118954145)
          ·
            refine ⟨9466394717156735339215609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12621859622875647118954145 9466394717156735339215609)
            ·
              refine ⟨7099796037867551504411707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9466394717156735339215609 7099796037867551504411707)
              ·
                refine ⟨10649694056801327256617561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7099796037867551504411707 10649694056801327256617561)
                ·
                  refine ⟨7987270542600995442463171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10649694056801327256617561 7987270542600995442463171)
                  ·
                    refine ⟨11980905813901493163694757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7987270542600995442463171 11980905813901493163694757)
                    ·
                      refine ⟨2246419840106529968192767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11980905813901493163694757 2246419840106529968192767)
                      ·
                        rfl

theorem cell23_4374887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 1, 2, 1, 4].length) (baseStart_4374887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4374887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4374887 prefixEnd_4374887 := by exact prefixLift 4374887
  have htrace : WordTrace (prefixWord ++ tailWord_4374887) baseStart_4374887 baseEnd_4374887 := by
    simpa [prefixWord, tailWord_4374887, baseEnd_4374887] using wordTrace_append hprefix tailTrace_4374887
  have hstable : (prefixWord ++ tailWord_4374887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4374887).length < 2 ^ (prefixWord ++ tailWord_4374887).sum := by decide
  have hdescent : baseEnd_4374887 < baseStart_4374887 := by decide
  rcases family_descends (prefixWord ++ tailWord_4374887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4374897 : List Nat := [1, 2, 2, 2, 1, 2, 1, 7, 1, 4]
def baseStart_4374897 : Nat := 118140960795 + 4374897 * 2 ^ 59
def prefixEnd_4374897 : Nat := 4983230072969 + 3 ^ 40 * 4374897 * 2
def baseEnd_4374897 : Nat := 748808324971024976355907

theorem tailTrace_4374897 : CollatzResearch.WordTrace tailWord_4374897 prefixEnd_4374897 748808324971024976355907 := by
  unfold tailWord_4374897
  simp only [CollatzResearch.WordTrace]
  refine ⟨159565602431502816767234945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106377068287668544511489963 159565602431502816767234945)
  ·
    refine ⟨119674201823627112575426209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159565602431502816767234945 119674201823627112575426209)
    ·
      refine ⟨89755651367720334431569657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119674201823627112575426209 89755651367720334431569657)
      ·
        refine ⟨67316738525790250823677243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89755651367720334431569657 67316738525790250823677243)
        ·
          refine ⟨100975107788685376235515865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67316738525790250823677243 100975107788685376235515865)
          ·
            refine ⟨75731330841514032176636899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100975107788685376235515865 75731330841514032176636899)
            ·
              refine ⟨113596996262271048264955349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75731330841514032176636899 113596996262271048264955349)
              ·
                refine ⟨2662429599896977693709891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 113596996262271048264955349 2662429599896977693709891)
                ·
                  refine ⟨3993644399845466540564837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2662429599896977693709891 3993644399845466540564837)
                  ·
                    refine ⟨748808324971024976355907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3993644399845466540564837 748808324971024976355907)
                    ·
                      rfl

theorem cell23_4374897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 7, 1, 4].length) (baseStart_4374897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4374897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4374897 prefixEnd_4374897 := by exact prefixLift 4374897
  have htrace : WordTrace (prefixWord ++ tailWord_4374897) baseStart_4374897 baseEnd_4374897 := by
    simpa [prefixWord, tailWord_4374897, baseEnd_4374897] using wordTrace_append hprefix tailTrace_4374897
  have hstable : (prefixWord ++ tailWord_4374897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4374897).length < 2 ^ (prefixWord ++ tailWord_4374897).sum := by decide
  have hdescent : baseEnd_4374897 < baseStart_4374897 := by decide
  rcases family_descends (prefixWord ++ tailWord_4374897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4374933 : List Nat := [1, 3, 2, 1, 1, 2, 1, 1, 1, 3, 7]
def baseStart_4374933 : Nat := 118140960795 + 4374933 * 2 ^ 59
def prefixEnd_4374933 : Nat := 4983230072969 + 3 ^ 40 * 4374933 * 2
def baseEnd_4374933 : Nat := 2246443460216636788217555

theorem tailTrace_4374933 : CollatzResearch.WordTrace tailWord_4374933 prefixEnd_4374933 2246443460216636788217555 := by
  unfold tailWord_4374933
  simp only [CollatzResearch.WordTrace]
  refine ⟨159566915459372394915545453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106377943639581596610363635 159566915459372394915545453)
  ·
    refine ⟨59837593297264648093329545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159566915459372394915545453 59837593297264648093329545)
    ·
      refine ⟨44878194972948486069997159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59837593297264648093329545 44878194972948486069997159)
      ·
        refine ⟨67317292459422729104995739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44878194972948486069997159 67317292459422729104995739)
        ·
          refine ⟨100975938689134093657493609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67317292459422729104995739 100975938689134093657493609)
          ·
            refine ⟨75731954016850570243120207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100975938689134093657493609 75731954016850570243120207)
            ·
              refine ⟨113597931025275855364680311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75731954016850570243120207 113597931025275855364680311)
              ·
                refine ⟨170396896537913783047020467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113597931025275855364680311 170396896537913783047020467)
                ·
                  refine ⟨255595344806870674570530701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 170396896537913783047020467 255595344806870674570530701)
                  ·
                    refine ⟨95848254302576502963949013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 255595344806870674570530701 95848254302576502963949013)
                    ·
                      refine ⟨2246443460216636788217555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 95848254302576502963949013 2246443460216636788217555)
                      ·
                        rfl

theorem cell23_4374933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_4374933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4374933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4374933 prefixEnd_4374933 := by exact prefixLift 4374933
  have htrace : WordTrace (prefixWord ++ tailWord_4374933) baseStart_4374933 baseEnd_4374933 := by
    simpa [prefixWord, tailWord_4374933, baseEnd_4374933] using wordTrace_append hprefix tailTrace_4374933
  have hstable : (prefixWord ++ tailWord_4374933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4374933).length < 2 ^ (prefixWord ++ tailWord_4374933).sum := by decide
  have hdescent : baseEnd_4374933 < baseStart_4374933 := by decide
  rcases family_descends (prefixWord ++ tailWord_4374933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4374937 : List Nat := [1, 2, 1, 2, 1, 4, 3, 2, 3, 1, 3]
def baseStart_4374937 : Nat := 118140960795 + 4374937 * 2 ^ 59
def prefixEnd_4374937 : Nat := 4983230072969 + 3 ^ 40 * 4374937 * 2
def baseEnd_4374937 : Nat := 2246445514139254772567537

theorem tailTrace_4374937 : CollatzResearch.WordTrace tailWord_4374937 prefixEnd_4374937 2246445514139254772567537 := by
  unfold tailWord_4374937
  simp only [CollatzResearch.WordTrace]
  refine ⟨159567061351357903598691065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106378040900905269065794043 159567061351357903598691065)
  ·
    refine ⟨119675296013518427699018299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159567061351357903598691065 119675296013518427699018299)
    ·
      refine ⟨179512944020277641548527449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119675296013518427699018299 179512944020277641548527449)
      ·
        refine ⟨134634708015208231161395587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179512944020277641548527449 134634708015208231161395587)
        ·
          refine ⟨201952062022812346742093381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134634708015208231161395587 201952062022812346742093381)
          ·
            refine ⟨37866011629277315014142509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 201952062022812346742093381 37866011629277315014142509)
            ·
              refine ⟨14199754360978993130303441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37866011629277315014142509 14199754360978993130303441)
              ·
                refine ⟨10649815770734244847727581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14199754360978993130303441 10649815770734244847727581)
                ·
                  refine ⟨3993680914025341817897843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10649815770734244847727581 3993680914025341817897843)
                  ·
                    refine ⟨5990521371038012726846765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3993680914025341817897843 5990521371038012726846765)
                    ·
                      refine ⟨2246445514139254772567537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5990521371038012726846765 2246445514139254772567537)
                      ·
                        rfl

theorem cell23_4374937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 2, 3, 1, 3].length) (baseStart_4374937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4374937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4374937 prefixEnd_4374937 := by exact prefixLift 4374937
  have htrace : WordTrace (prefixWord ++ tailWord_4374937) baseStart_4374937 baseEnd_4374937 := by
    simpa [prefixWord, tailWord_4374937, baseEnd_4374937] using wordTrace_append hprefix tailTrace_4374937
  have hstable : (prefixWord ++ tailWord_4374937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4374937).length < 2 ^ (prefixWord ++ tailWord_4374937).sum := by decide
  have hdescent : baseEnd_4374937 < baseStart_4374937 := by decide
  rcases family_descends (prefixWord ++ tailWord_4374937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4374941 : List Nat := [1, 4, 2, 1, 5, 1, 1, 1, 2, 2, 3]
def baseStart_4374941 : Nat := 118140960795 + 4374941 * 2 ^ 59
def prefixEnd_4374941 : Nat := 4983230072969 + 3 ^ 40 * 4374941 * 2
def baseEnd_4374941 : Nat := 2246447568061872756917519

theorem tailTrace_4374941 : CollatzResearch.WordTrace tailWord_4374941 prefixEnd_4374941 2246447568061872756917519 := by
  unfold tailWord_4374941
  simp only [CollatzResearch.WordTrace]
  refine ⟨159567207243343412281836677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106378138162228941521224451 159567207243343412281836677)
  ·
    refine ⟨29918851358126889802844377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 159567207243343412281836677 29918851358126889802844377)
    ·
      refine ⟨22439138518595167352133283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29918851358126889802844377 22439138518595167352133283)
      ·
        refine ⟨33658707777892751028199925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22439138518595167352133283 33658707777892751028199925)
        ·
          refine ⟨3155503854177445408893743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33658707777892751028199925 3155503854177445408893743)
          ·
            refine ⟨4733255781266168113340615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3155503854177445408893743 4733255781266168113340615)
            ·
              refine ⟨7099883671899252170010923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4733255781266168113340615 7099883671899252170010923)
              ·
                refine ⟨10649825507848878255016385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7099883671899252170010923 10649825507848878255016385)
                ·
                  refine ⟨7987369130886658691262289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10649825507848878255016385 7987369130886658691262289)
                  ·
                    refine ⟨5990526848164994018446717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7987369130886658691262289 5990526848164994018446717)
                    ·
                      refine ⟨2246447568061872756917519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5990526848164994018446717 2246447568061872756917519)
                      ·
                        rfl

theorem cell23_4374941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 1, 2, 2, 3].length) (baseStart_4374941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4374941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4374941 prefixEnd_4374941 := by exact prefixLift 4374941
  have htrace : WordTrace (prefixWord ++ tailWord_4374941) baseStart_4374941 baseEnd_4374941 := by
    simpa [prefixWord, tailWord_4374941, baseEnd_4374941] using wordTrace_append hprefix tailTrace_4374941
  have hstable : (prefixWord ++ tailWord_4374941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4374941).length < 2 ^ (prefixWord ++ tailWord_4374941).sum := by decide
  have hdescent : baseEnd_4374941 < baseStart_4374941 := by decide
  rcases family_descends (prefixWord ++ tailWord_4374941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4374947 : List Nat := [1, 1, 1, 4, 1, 5, 1, 1, 1, 5, 2]
def baseStart_4374947 : Nat := 118140960795 + 4374947 * 2 ^ 59
def prefixEnd_4374947 : Nat := 4983230072969 + 3 ^ 40 * 4374947 * 2
def baseEnd_4374947 : Nat := 2246450648945799733442491

theorem tailTrace_4374947 : CollatzResearch.WordTrace tailWord_4374947 prefixEnd_4374947 2246450648945799733442491 := by
  unfold tailWord_4374947
  simp only [CollatzResearch.WordTrace]
  refine ⟨159567426081321675306555095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106378284054214450204370063 159567426081321675306555095)
  ·
    refine ⟨239351139121982512959832643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159567426081321675306555095 239351139121982512959832643)
    ·
      refine ⟨359026708682973769439748965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239351139121982512959832643 359026708682973769439748965)
      ·
        refine ⟨67317507878057581769952931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 359026708682973769439748965 67317507878057581769952931)
        ·
          refine ⟨100976261817086372654929397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67317507878057581769952931 100976261817086372654929397)
          ·
            refine ⟨9466524545351847436399631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 100976261817086372654929397 9466524545351847436399631)
            ·
              refine ⟨14199786818027771154599447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9466524545351847436399631 14199786818027771154599447)
              ·
                refine ⟨21299680227041656731899171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14199786818027771154599447 21299680227041656731899171)
                ·
                  refine ⟨31949520340562485097848757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21299680227041656731899171 31949520340562485097848757)
                  ·
                    refine ⟨2995267531927732977923321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31949520340562485097848757 2995267531927732977923321)
                    ·
                      refine ⟨2246450648945799733442491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2995267531927732977923321 2246450648945799733442491)
                      ·
                        rfl

theorem cell23_4374947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 5, 2].length) (baseStart_4374947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4374947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4374947 prefixEnd_4374947 := by exact prefixLift 4374947
  have htrace : WordTrace (prefixWord ++ tailWord_4374947) baseStart_4374947 baseEnd_4374947 := by
    simpa [prefixWord, tailWord_4374947, baseEnd_4374947] using wordTrace_append hprefix tailTrace_4374947
  have hstable : (prefixWord ++ tailWord_4374947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4374947).length < 2 ^ (prefixWord ++ tailWord_4374947).sum := by decide
  have hdescent : baseEnd_4374947 < baseStart_4374947 := by decide
  rcases family_descends (prefixWord ++ tailWord_4374947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4375027 : List Nat := [1, 1, 1, 2, 2, 2, 3, 3, 4, 1, 3]
def baseStart_4375027 : Nat := 118140960795 + 4375027 * 2 ^ 59
def prefixEnd_4375027 : Nat := 4983230072969 + 3 ^ 40 * 4375027 * 2
def baseEnd_4375027 : Nat := 2246491727398159420442123

theorem tailTrace_4375027 : CollatzResearch.WordTrace tailWord_4375027 prefixEnd_4375027 2246491727398159420442123 := by
  unfold tailWord_4375027
  simp only [CollatzResearch.WordTrace]
  refine ⟨159570343921031848969467335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106380229280687899312978223 159570343921031848969467335)
  ·
    refine ⟨239355515881547773454201003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159570343921031848969467335 239355515881547773454201003)
    ·
      refine ⟨359033273822321660181301505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239355515881547773454201003 359033273822321660181301505)
      ·
        refine ⟨269274955366741245135976129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 359033273822321660181301505 269274955366741245135976129)
        ·
          refine ⟨201956216525055933851982097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 269274955366741245135976129 201956216525055933851982097)
          ·
            refine ⟨151467162393791950388986573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 201956216525055933851982097 151467162393791950388986573)
            ·
              refine ⟨56800185897671981395869965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 151467162393791950388986573 56800185897671981395869965)
              ·
                refine ⟨21300069711626993023451237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56800185897671981395869965 21300069711626993023451237)
                ·
                  refine ⟨3993763070930061191897107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21300069711626993023451237 3993763070930061191897107)
                  ·
                    refine ⟨5990644606395091787845661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3993763070930061191897107 5990644606395091787845661)
                    ·
                      refine ⟨2246491727398159420442123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5990644606395091787845661 2246491727398159420442123)
                      ·
                        rfl

theorem cell23_4375027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 4, 1, 3].length) (baseStart_4375027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4375027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4375027 prefixEnd_4375027 := by exact prefixLift 4375027
  have htrace : WordTrace (prefixWord ++ tailWord_4375027) baseStart_4375027 baseEnd_4375027 := by
    simpa [prefixWord, tailWord_4375027, baseEnd_4375027] using wordTrace_append hprefix tailTrace_4375027
  have hstable : (prefixWord ++ tailWord_4375027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4375027).length < 2 ^ (prefixWord ++ tailWord_4375027).sum := by decide
  have hdescent : baseEnd_4375027 < baseStart_4375027 := by decide
  rcases family_descends (prefixWord ++ tailWord_4375027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4375079 : List Nat := [1, 1, 7, 2, 1, 2, 2, 2, 1, 2, 2]
def baseStart_4375079 : Nat := 118140960795 + 4375079 * 2 ^ 59
def prefixEnd_4375079 : Nat := 4983230072969 + 3 ^ 40 * 4375079 * 2
def baseEnd_4375079 : Nat := 2246518428392193216991885

theorem tailTrace_4375079 : CollatzResearch.WordTrace tailWord_4375079 prefixEnd_4375079 2246518428392193216991885 := by
  unfold tailWord_4375079
  simp only [CollatzResearch.WordTrace]
  refine ⟨159572240516843461850360291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106381493677895641233573527 159572240516843461850360291)
  ·
    refine ⟨239358360775265192775540437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159572240516843461850360291 239358360775265192775540437)
    ·
      refine ⟨5609961580670277955676729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 239358360775265192775540437 5609961580670277955676729)
      ·
        refine ⟨4207471185502708466757547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5609961580670277955676729 4207471185502708466757547)
        ·
          refine ⟨6311206778254062700136321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4207471185502708466757547 6311206778254062700136321)
          ·
            refine ⟨4733405083690547025102241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6311206778254062700136321 4733405083690547025102241)
            ·
              refine ⟨3550053812767910268826681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4733405083690547025102241 3550053812767910268826681)
              ·
                refine ⟨2662540359575932701620011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3550053812767910268826681 2662540359575932701620011)
                ·
                  refine ⟨3993810539363899052430017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2662540359575932701620011 3993810539363899052430017)
                  ·
                    refine ⟨2995357904522924289322513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3993810539363899052430017 2995357904522924289322513)
                    ·
                      refine ⟨2246518428392193216991885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2995357904522924289322513 2246518428392193216991885)
                      ·
                        rfl

theorem cell23_4375079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_4375079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4375079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4375079 prefixEnd_4375079 := by exact prefixLift 4375079
  have htrace : WordTrace (prefixWord ++ tailWord_4375079) baseStart_4375079 baseEnd_4375079 := by
    simpa [prefixWord, tailWord_4375079, baseEnd_4375079] using wordTrace_append hprefix tailTrace_4375079
  have hstable : (prefixWord ++ tailWord_4375079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4375079).length < 2 ^ (prefixWord ++ tailWord_4375079).sum := by decide
  have hdescent : baseEnd_4375079 < baseStart_4375079 := by decide
  rcases family_descends (prefixWord ++ tailWord_4375079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4375084 : List Nat := [2, 2, 1, 1, 1, 2, 1, 5, 4, 2, 2]
def baseStart_4375084 : Nat := 118140960795 + 4375084 * 2 ^ 59
def prefixEnd_4375084 : Nat := 4983230072969 + 3 ^ 40 * 4375084 * 2
def baseEnd_4375084 : Nat := 2246520995795465697429361

theorem tailTrace_4375084 : CollatzResearch.WordTrace tailWord_4375084 prefixEnd_4375084 2246520995795465697429361 := by
  unfold tailWord_4375084
  simp only [CollatzResearch.WordTrace]
  refine ⟨79786211440912673852146153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106381615254550231802861537 79786211440912673852146153)
  ·
    refine ⟨59839658580684505389109615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79786211440912673852146153 59839658580684505389109615)
    ·
      refine ⟨89759487871026758083664423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59839658580684505389109615 89759487871026758083664423)
      ·
        refine ⟨134639231806540137125496635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89759487871026758083664423 134639231806540137125496635)
        ·
          refine ⟨201958847709810205688244953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134639231806540137125496635 201958847709810205688244953)
          ·
            refine ⟨151469135782357654266183715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 201958847709810205688244953 151469135782357654266183715)
            ·
              refine ⟨227203703673536481399275573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151469135782357654266183715 227203703673536481399275573)
              ·
                refine ⟨21300347219394045131182085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 227203703673536481399275573 21300347219394045131182085)
                ·
                  refine ⟨3993815103636383462096641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21300347219394045131182085 3993815103636383462096641)
                  ·
                    refine ⟨2995361327727287596572481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3993815103636383462096641 2995361327727287596572481)
                    ·
                      refine ⟨2246520995795465697429361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2995361327727287596572481 2246520995795465697429361)
                      ·
                        rfl

theorem cell23_4375084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 2, 2].length) (baseStart_4375084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4375084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4375084 prefixEnd_4375084 := by exact prefixLift 4375084
  have htrace : WordTrace (prefixWord ++ tailWord_4375084) baseStart_4375084 baseEnd_4375084 := by
    simpa [prefixWord, tailWord_4375084, baseEnd_4375084] using wordTrace_append hprefix tailTrace_4375084
  have hstable : (prefixWord ++ tailWord_4375084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4375084).length < 2 ^ (prefixWord ++ tailWord_4375084).sum := by decide
  have hdescent : baseEnd_4375084 < baseStart_4375084 := by decide
  rcases family_descends (prefixWord ++ tailWord_4375084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4375094 : List Nat := [5, 1, 2, 1, 2, 2, 1, 1, 2, 6]
def baseStart_4375094 : Nat := 118140960795 + 4375094 * 2 ^ 59
def prefixEnd_4375094 : Nat := 4983230072969 + 3 ^ 40 * 4375094 * 2
def baseEnd_4375094 : Nat := 748842043534003552768105

theorem tailTrace_4375094 : CollatzResearch.WordTrace tailWord_4375094 prefixEnd_4375094 748842043534003552768105 := by
  unfold tailWord_4375094
  simp only [CollatzResearch.WordTrace]
  refine ⟨9973299225736819963259771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 106381858407859412941437557 9973299225736819963259771)
  ·
    refine ⟨14959948838605229944889657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9973299225736819963259771 14959948838605229944889657)
    ·
      refine ⟨11219961628953922458667243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14959948838605229944889657 11219961628953922458667243)
      ·
        refine ⟨16829942443430883688000865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11219961628953922458667243 16829942443430883688000865)
        ·
          refine ⟨12622456832573162766000649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16829942443430883688000865 12622456832573162766000649)
          ·
            refine ⟨9466842624429872074500487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12622456832573162766000649 9466842624429872074500487)
            ·
              refine ⟨14200263936644808111750731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9466842624429872074500487 14200263936644808111750731)
              ·
                refine ⟨21300395904967212167626097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14200263936644808111750731 21300395904967212167626097)
                ·
                  refine ⟨15975296928725409125719573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21300395904967212167626097 15975296928725409125719573)
                  ·
                    refine ⟨748842043534003552768105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15975296928725409125719573 748842043534003552768105)
                    ·
                      rfl

theorem cell23_4375094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_4375094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4375094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4375094 prefixEnd_4375094 := by exact prefixLift 4375094
  have htrace : WordTrace (prefixWord ++ tailWord_4375094) baseStart_4375094 baseEnd_4375094 := by
    simpa [prefixWord, tailWord_4375094, baseEnd_4375094] using wordTrace_append hprefix tailTrace_4375094
  have hstable : (prefixWord ++ tailWord_4375094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4375094).length < 2 ^ (prefixWord ++ tailWord_4375094).sum := by decide
  have hdescent : baseEnd_4375094 < baseStart_4375094 := by decide
  rcases family_descends (prefixWord ++ tailWord_4375094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4375097 : List Nat := [1, 2, 1, 5, 1, 1, 3, 1, 2, 2, 4]
def baseStart_4375097 : Nat := 118140960795 + 4375097 * 2 ^ 59
def prefixEnd_4375097 : Nat := 4983230072969 + 3 ^ 40 * 4375097 * 2
def baseEnd_4375097 : Nat := 2246527671043974146566801

theorem tailTrace_4375097 : CollatzResearch.WordTrace tailWord_4375097 prefixEnd_4375097 2246527671043974146566801 := by
  unfold tailWord_4375097
  simp only [CollatzResearch.WordTrace]
  refine ⟨159572897030778250924515545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106381931353852167283010363 159572897030778250924515545)
  ·
    refine ⟨119679672773083688193386659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159572897030778250924515545 119679672773083688193386659)
    ·
      refine ⟨179519509159625532290079989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119679672773083688193386659 179519509159625532290079989)
      ·
        refine ⟨16829953983714893652194999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 179519509159625532290079989 16829953983714893652194999)
        ·
          refine ⟨25244930975572340478292499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16829953983714893652194999 25244930975572340478292499)
          ·
            refine ⟨37867396463358510717438749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25244930975572340478292499 37867396463358510717438749)
            ·
              refine ⟨14200273673759441519039531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37867396463358510717438749 14200273673759441519039531)
              ·
                refine ⟨21300410510639162278559297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14200273673759441519039531 21300410510639162278559297)
                ·
                  refine ⟨15975307882979371708919473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21300410510639162278559297 15975307882979371708919473)
                  ·
                    refine ⟨11981480912234528781689605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15975307882979371708919473 11981480912234528781689605)
                    ·
                      refine ⟨2246527671043974146566801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11981480912234528781689605 2246527671043974146566801)
                      ·
                        rfl

theorem cell23_4375097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_4375097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4375097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4375097 prefixEnd_4375097 := by exact prefixLift 4375097
  have htrace : WordTrace (prefixWord ++ tailWord_4375097) baseStart_4375097 baseEnd_4375097 := by
    simpa [prefixWord, tailWord_4375097, baseEnd_4375097] using wordTrace_append hprefix tailTrace_4375097
  have hstable : (prefixWord ++ tailWord_4375097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4375097).length < 2 ^ (prefixWord ++ tailWord_4375097).sum := by decide
  have hdescent : baseEnd_4375097 < baseStart_4375097 := by decide
  rcases family_descends (prefixWord ++ tailWord_4375097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4375101 : List Nat := [1, 4, 1, 3, 2, 2, 2, 1, 1, 4, 2]
def baseStart_4375101 : Nat := 118140960795 + 4375101 * 2 ^ 59
def prefixEnd_4375101 : Nat := 4983230072969 + 3 ^ 40 * 4375101 * 2
def baseEnd_4375101 : Nat := 2246529724966592130916783

theorem tailTrace_4375101 : CollatzResearch.WordTrace tailWord_4375101 prefixEnd_4375101 2246529724966592130916783 := by
  unfold tailWord_4375101
  simp only [CollatzResearch.WordTrace]
  refine ⟨159573042922763759607661157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106382028615175839738440771 159573042922763759607661157)
  ·
    refine ⟨29919945548018204926436467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 159573042922763759607661157 29919945548018204926436467)
    ·
      refine ⟨44879918322027307389654701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29919945548018204926436467 44879918322027307389654701)
      ·
        refine ⟨16829969370760240271120513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44879918322027307389654701 16829969370760240271120513)
        ·
          refine ⟨12622477028070180203340385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16829969370760240271120513 12622477028070180203340385)
          ·
            refine ⟨9466857771052635152505289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12622477028070180203340385 9466857771052635152505289)
            ·
              refine ⟨7100143328289476364378967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9466857771052635152505289 7100143328289476364378967)
              ·
                refine ⟨10650214992434214546568451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7100143328289476364378967 10650214992434214546568451)
                ·
                  refine ⟨15975322488651321819852677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10650214992434214546568451 15975322488651321819852677)
                  ·
                    refine ⟨2995372966622122841222377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15975322488651321819852677 2995372966622122841222377)
                    ·
                      refine ⟨2246529724966592130916783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2995372966622122841222377 2246529724966592130916783)
                      ·
                        rfl

theorem cell23_4375101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 1, 1, 4, 2].length) (baseStart_4375101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4375101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4375101 prefixEnd_4375101 := by exact prefixLift 4375101
  have htrace : WordTrace (prefixWord ++ tailWord_4375101) baseStart_4375101 baseEnd_4375101 := by
    simpa [prefixWord, tailWord_4375101, baseEnd_4375101] using wordTrace_append hprefix tailTrace_4375101
  have hstable : (prefixWord ++ tailWord_4375101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4375101).length < 2 ^ (prefixWord ++ tailWord_4375101).sum := by decide
  have hdescent : baseEnd_4375101 < baseStart_4375101 := by decide
  rcases family_descends (prefixWord ++ tailWord_4375101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4375124 : List Nat := [2, 4, 1, 1, 1, 3, 1, 5, 5]
def baseStart_4375124 : Nat := 118140960795 + 4375124 * 2 ^ 59
def prefixEnd_4375124 : Nat := 4983230072969 + 3 ^ 40 * 4375124 * 2
def baseEnd_4375124 : Nat := 249615726113516171214353

theorem tailTrace_4375124 : CollatzResearch.WordTrace tailWord_4375124 prefixEnd_4375124 249615726113516171214353 := by
  unfold tailWord_4375124
  simp only [CollatzResearch.WordTrace]
  refine ⟨79786940900840217267874213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106382587867786956357165617 79786940900840217267874213)
  ·
    refine ⟨14960051418907540737726415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79786940900840217267874213 14960051418907540737726415)
    ·
      refine ⟨22440077128361311106589623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14960051418907540737726415 22440077128361311106589623)
      ·
        refine ⟨33660115692541966659884435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22440077128361311106589623 33660115692541966659884435)
        ·
          refine ⟨50490173538812949989826653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33660115692541966659884435 50490173538812949989826653)
          ·
            refine ⟨18933815077054856246184995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50490173538812949989826653 18933815077054856246184995)
            ·
              refine ⟨28400722615582284369277493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18933815077054856246184995 28400722615582284369277493)
              ·
                refine ⟨2662567745210839159619765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28400722615582284369277493 2662567745210839159619765)
                ·
                  refine ⟨249615726113516171214353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2662567745210839159619765 249615726113516171214353)
                  ·
                    rfl

theorem cell23_4375124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 5, 5].length) (baseStart_4375124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4375124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4375124 prefixEnd_4375124 := by exact prefixLift 4375124
  have htrace : WordTrace (prefixWord ++ tailWord_4375124) baseStart_4375124 baseEnd_4375124 := by
    simpa [prefixWord, tailWord_4375124, baseEnd_4375124] using wordTrace_append hprefix tailTrace_4375124
  have hstable : (prefixWord ++ tailWord_4375124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4375124).length < 2 ^ (prefixWord ++ tailWord_4375124).sum := by decide
  have hdescent : baseEnd_4375124 < baseStart_4375124 := by decide
  rcases family_descends (prefixWord ++ tailWord_4375124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4375167 : List Nat := [1, 1, 2, 2, 1, 1, 1, 5, 5, 4]
def baseStart_4375167 : Nat := 118140960795 + 4375167 * 2 ^ 59
def prefixEnd_4375167 : Nat := 4983230072969 + 3 ^ 40 * 4375167 * 2
def baseEnd_4375167 : Nat := 748854538229929624230493

theorem tailTrace_4375167 : CollatzResearch.WordTrace tailWord_4375167 prefixEnd_4375167 748854538229929624230493 := by
  unfold tailWord_4375167
  simp only [CollatzResearch.WordTrace]
  refine ⟨159575450140524652879563755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106383633427016435253042503 159575450140524652879563755)
  ·
    refine ⟨239363175210786979319345633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159575450140524652879563755 239363175210786979319345633)
    ·
      refine ⟨179522381408090234489509225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 239363175210786979319345633 179522381408090234489509225)
      ·
        refine ⟨134641786056067675867131919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179522381408090234489509225 134641786056067675867131919)
        ·
          refine ⟨201962679084101513800697879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134641786056067675867131919 201962679084101513800697879)
          ·
            refine ⟨302944018626152270701046819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201962679084101513800697879 302944018626152270701046819)
            ·
              refine ⟨454416027939228406051570229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 302944018626152270701046819 454416027939228406051570229)
              ·
                refine ⟨42601502619302663067334709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 454416027939228406051570229 42601502619302663067334709)
                ·
                  refine ⟨3993890870559624662562629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42601502619302663067334709 3993890870559624662562629)
                  ·
                    refine ⟨748854538229929624230493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3993890870559624662562629 748854538229929624230493)
                    ·
                      rfl

theorem cell23_4375167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 5, 4].length) (baseStart_4375167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4375167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4375167 prefixEnd_4375167 := by exact prefixLift 4375167
  have htrace : WordTrace (prefixWord ++ tailWord_4375167) baseStart_4375167 baseEnd_4375167 := by
    simpa [prefixWord, tailWord_4375167, baseEnd_4375167] using wordTrace_append hprefix tailTrace_4375167
  have hstable : (prefixWord ++ tailWord_4375167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4375167).length < 2 ^ (prefixWord ++ tailWord_4375167).sum := by decide
  have hdescent : baseEnd_4375167 < baseStart_4375167 := by decide
  rcases family_descends (prefixWord ++ tailWord_4375167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4375197 : List Nat := [1, 4, 2, 1, 1, 1, 4, 1, 8]
def baseStart_4375197 : Nat := 118140960795 + 4375197 * 2 ^ 59
def prefixEnd_4375197 : Nat := 4983230072969 + 3 ^ 40 * 4375197 * 2
def baseEnd_4375197 : Nat := 249619891012158195035149

theorem tailTrace_4375197 : CollatzResearch.WordTrace tailWord_4375197 prefixEnd_4375197 249619891012158195035149 := by
  unfold tailWord_4375197
  simp only [CollatzResearch.WordTrace]
  refine ⟨159576544330415968003155845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106384362886943978668770563 159576544330415968003155845)
  ·
    refine ⟨29920602061952994000591721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 159576544330415968003155845 29920602061952994000591721)
    ·
      refine ⟨22440451546464745500443791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29920602061952994000591721 22440451546464745500443791)
      ·
        refine ⟨33660677319697118250665687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22440451546464745500443791 33660677319697118250665687)
        ·
          refine ⟨50491015979545677375998531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33660677319697118250665687 50491015979545677375998531)
          ·
            refine ⟨75736523969318516063997797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50491015979545677375998531 75736523969318516063997797)
            ·
              refine ⟨14200598244247221761999587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75736523969318516063997797 14200598244247221761999587)
              ·
                refine ⟨21300897366370832642999381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14200598244247221761999587 21300897366370832642999381)
                ·
                  refine ⟨249619891012158195035149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21300897366370832642999381 249619891012158195035149)
                  ·
                    rfl

theorem cell23_4375197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 8].length) (baseStart_4375197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4375197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4375197 prefixEnd_4375197 := by exact prefixLift 4375197
  have htrace : WordTrace (prefixWord ++ tailWord_4375197) baseStart_4375197 baseEnd_4375197 := by
    simpa [prefixWord, tailWord_4375197, baseEnd_4375197] using wordTrace_append hprefix tailTrace_4375197
  have hstable : (prefixWord ++ tailWord_4375197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4375197).length < 2 ^ (prefixWord ++ tailWord_4375197).sum := by decide
  have hdescent : baseEnd_4375197 < baseStart_4375197 := by decide
  rcases family_descends (prefixWord ++ tailWord_4375197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4375252 : List Nat := [2, 4, 1, 3, 2, 2, 2, 2, 1, 4]
def baseStart_4375252 : Nat := 118140960795 + 4375252 * 2 ^ 59
def prefixEnd_4375252 : Nat := 4983230072969 + 3 ^ 40 * 4375252 * 2
def baseEnd_4375252 : Nat := 748869086848473680042863

theorem tailTrace_4375252 : CollatzResearch.WordTrace tailWord_4375252 prefixEnd_4375252 748869086848473680042863 := by
  unfold tailWord_4375252
  simp only [CollatzResearch.WordTrace]
  refine ⟨79789275172608356198204005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106385700230144474930938673 79789275172608356198204005)
  ·
    refine ⟨14960489094864066787163251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79789275172608356198204005 14960489094864066787163251)
    ·
      refine ⟨22440733642296100180744877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14960489094864066787163251 22440733642296100180744877)
      ·
        refine ⟨8415275115861037567779329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22440733642296100180744877 8415275115861037567779329)
        ·
          refine ⟨6311456336895778175834497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8415275115861037567779329 6311456336895778175834497)
          ·
            refine ⟨4733592252671833631875873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6311456336895778175834497 4733592252671833631875873)
            ·
              refine ⟨3550194189503875223906905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4733592252671833631875873 3550194189503875223906905)
              ·
                refine ⟨2662645642127906417930179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3550194189503875223906905 2662645642127906417930179)
                ·
                  refine ⟨3993968463191859626895269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2662645642127906417930179 3993968463191859626895269)
                  ·
                    refine ⟨748869086848473680042863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3993968463191859626895269 748869086848473680042863)
                    ·
                      rfl

theorem cell23_4375252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 2, 2, 1, 4].length) (baseStart_4375252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4375252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4375252 prefixEnd_4375252 := by exact prefixLift 4375252
  have htrace : WordTrace (prefixWord ++ tailWord_4375252) baseStart_4375252 baseEnd_4375252 := by
    simpa [prefixWord, tailWord_4375252, baseEnd_4375252] using wordTrace_append hprefix tailTrace_4375252
  have hstable : (prefixWord ++ tailWord_4375252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4375252).length < 2 ^ (prefixWord ++ tailWord_4375252).sum := by decide
  have hdescent : baseEnd_4375252 < baseStart_4375252 := by decide
  rcases family_descends (prefixWord ++ tailWord_4375252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4375257 : List Nat := [1, 2, 1, 2, 3, 2, 1, 2, 3, 6]
def baseStart_4375257 : Nat := 118140960795 + 4375257 * 2 ^ 59
def prefixEnd_4375257 : Nat := 4983230072969 + 3 ^ 40 * 4375257 * 2
def baseEnd_4375257 : Nat := 748869942649564506855355

theorem tailTrace_4375257 : CollatzResearch.WordTrace tailWord_4375257 prefixEnd_4375257 748869942649564506855355 := by
  unfold tailWord_4375257
  simp only [CollatzResearch.WordTrace]
  refine ⟨159578732710198598250340025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106385821806799065500226683 159578732710198598250340025)
  ·
    refine ⟨119684049532648948687755019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159578732710198598250340025 119684049532648948687755019)
    ·
      refine ⟨179526074298973423031632529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119684049532648948687755019 179526074298973423031632529)
      ·
        refine ⟨134644555724230067273724397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179526074298973423031632529 134644555724230067273724397)
        ·
          refine ⟨50491708396586275227646649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134644555724230067273724397 50491708396586275227646649)
          ·
            refine ⟨37868781297439706420734987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50491708396586275227646649 37868781297439706420734987)
            ·
              refine ⟨56803171946159559631102481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37868781297439706420734987 56803171946159559631102481)
              ·
                refine ⟨42602378959619669723326861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56803171946159559631102481 42602378959619669723326861)
                ·
                  refine ⟨15975892109857376146247573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42602378959619669723326861 15975892109857376146247573)
                  ·
                    refine ⟨748869942649564506855355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15975892109857376146247573 748869942649564506855355)
                    ·
                      rfl

theorem cell23_4375257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 3, 6].length) (baseStart_4375257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4375257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4375257 prefixEnd_4375257 := by exact prefixLift 4375257
  have htrace : WordTrace (prefixWord ++ tailWord_4375257) baseStart_4375257 baseEnd_4375257 := by
    simpa [prefixWord, tailWord_4375257, baseEnd_4375257] using wordTrace_append hprefix tailTrace_4375257
  have hstable : (prefixWord ++ tailWord_4375257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4375257).length < 2 ^ (prefixWord ++ tailWord_4375257).sum := by decide
  have hdescent : baseEnd_4375257 < baseStart_4375257 := by decide
  rcases family_descends (prefixWord ++ tailWord_4375257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4375258 : List Nat := [3, 1, 1, 2, 2, 2, 3, 4, 1, 1, 3]
def baseStart_4375258 : Nat := 118140960795 + 4375258 * 2 ^ 59
def prefixEnd_4375258 : Nat := 4983230072969 + 3 ^ 40 * 4375258 * 2
def baseEnd_4375258 : Nat := 2246610341429348016653561

theorem tailTrace_4375258 : CollatzResearch.WordTrace tailWord_4375258 prefixEnd_4375258 2246610341429348016653561 := by
  unfold tailWord_4375258
  simp only [CollatzResearch.WordTrace]
  refine ⟨39894692295798743855281607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106385846122129983614084285 39894692295798743855281607)
  ·
    refine ⟨59842038443698115782922411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39894692295798743855281607 59842038443698115782922411)
    ·
      refine ⟨89763057665547173674383617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59842038443698115782922411 89763057665547173674383617)
      ·
        refine ⟨67322293249160380255787713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89763057665547173674383617 67322293249160380255787713)
        ·
          refine ⟨50491719936870285191840785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67322293249160380255787713 50491719936870285191840785)
          ·
            refine ⟨37868789952652713893880589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50491719936870285191840785 37868789952652713893880589)
            ·
              refine ⟨14200796232244767710205221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37868789952652713893880589 14200796232244767710205221)
              ·
                refine ⟨2662649293545893945663479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14200796232244767710205221 2662649293545893945663479)
                ·
                  refine ⟨3993973940318840918495219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2662649293545893945663479 3993973940318840918495219)
                  ·
                    refine ⟨5990960910478261377742829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3993973940318840918495219 5990960910478261377742829)
                    ·
                      refine ⟨2246610341429348016653561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5990960910478261377742829 2246610341429348016653561)
                      ·
                        rfl

theorem cell23_4375258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 4, 1, 1, 3].length) (baseStart_4375258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4375258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4375258 prefixEnd_4375258 := by exact prefixLift 4375258
  have htrace : WordTrace (prefixWord ++ tailWord_4375258) baseStart_4375258 baseEnd_4375258 := by
    simpa [prefixWord, tailWord_4375258, baseEnd_4375258] using wordTrace_append hprefix tailTrace_4375258
  have hstable : (prefixWord ++ tailWord_4375258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4375258).length < 2 ^ (prefixWord ++ tailWord_4375258).sum := by decide
  have hdescent : baseEnd_4375258 < baseStart_4375258 := by decide
  rcases family_descends (prefixWord ++ tailWord_4375258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4375264 : List Nat := [2, 1, 1, 3, 1, 2, 1, 2, 2, 6, 2]
def baseStart_4375264 : Nat := 118140960795 + 4375264 * 2 ^ 59
def prefixEnd_4375264 : Nat := 4983230072969 + 3 ^ 40 * 4375264 * 2
def baseEnd_4375264 : Nat := 2246613422313274993178533

theorem tailTrace_4375264 : CollatzResearch.WordTrace tailWord_4375264 prefixEnd_4375264 2246613422313274993178533 := by
  unfold tailWord_4375264
  simp only [CollatzResearch.WordTrace]
  refine ⟨79789494010586619222922423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106385992014115492297229897 79789494010586619222922423)
  ·
    refine ⟨119684241015879928834383635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79789494010586619222922423 119684241015879928834383635)
    ·
      refine ⟨179526361523819893251575453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119684241015879928834383635 179526361523819893251575453)
      ·
        refine ⟨67322385571432459969340795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 179526361523819893251575453 67322385571432459969340795)
        ·
          refine ⟨100983578357148689954011193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67322385571432459969340795 100983578357148689954011193)
          ·
            refine ⟨75737683767861517465508395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100983578357148689954011193 75737683767861517465508395)
            ·
              refine ⟨113606525651792276198262593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75737683767861517465508395 113606525651792276198262593)
              ·
                refine ⟨85204894238844207148696945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113606525651792276198262593 85204894238844207148696945)
                ·
                  refine ⟨63903670679133155361522709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85204894238844207148696945 63903670679133155361522709)
                  ·
                    refine ⟨2995484563084366657571377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 63903670679133155361522709 2995484563084366657571377)
                    ·
                      refine ⟨2246613422313274993178533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2995484563084366657571377 2246613422313274993178533)
                      ·
                        rfl

theorem cell23_4375264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 2, 6, 2].length) (baseStart_4375264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4375264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4375264 prefixEnd_4375264 := by exact prefixLift 4375264
  have htrace : WordTrace (prefixWord ++ tailWord_4375264) baseStart_4375264 baseEnd_4375264 := by
    simpa [prefixWord, tailWord_4375264, baseEnd_4375264] using wordTrace_append hprefix tailTrace_4375264
  have hstable : (prefixWord ++ tailWord_4375264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4375264).length < 2 ^ (prefixWord ++ tailWord_4375264).sum := by decide
  have hdescent : baseEnd_4375264 < baseStart_4375264 := by decide
  rcases family_descends (prefixWord ++ tailWord_4375264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4375274 : List Nat := [3, 1, 3, 1, 1, 1, 1, 2, 6, 4]
def baseStart_4375274 : Nat := 118140960795 + 4375274 * 2 ^ 59
def prefixEnd_4375274 : Nat := 4983230072969 + 3 ^ 40 * 4375274 * 2
def baseEnd_4375274 : Nat := 748872852373273318017829

theorem tailTrace_4375274 : CollatzResearch.WordTrace tailWord_4375274 prefixEnd_4375274 748872852373273318017829 := by
  unfold tailWord_4375274
  simp only [CollatzResearch.WordTrace]
  refine ⟨39894838187784252538427219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106386235167424673435805917 39894838187784252538427219)
  ·
    refine ⟨59842257281676378807640829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39894838187784252538427219 59842257281676378807640829)
    ·
      refine ⟨22440846480628642052865311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59842257281676378807640829 22440846480628642052865311)
      ·
        refine ⟨33661269720942963079297967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22440846480628642052865311 33661269720942963079297967)
        ·
          refine ⟨50491904581414444618946951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33661269720942963079297967 50491904581414444618946951)
          ·
            refine ⟨75737856872121666928420427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50491904581414444618946951 75737856872121666928420427)
            ·
              refine ⟨113606785308182500392630641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75737856872121666928420427 113606785308182500392630641)
              ·
                refine ⟨85205088981136875294472981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113606785308182500392630641 85205088981136875294472981)
                ·
                  refine ⟨3993988545990791029428421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 85205088981136875294472981 3993988545990791029428421)
                  ·
                    refine ⟨748872852373273318017829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3993988545990791029428421 748872852373273318017829)
                    ·
                      rfl

theorem cell23_4375274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 6, 4].length) (baseStart_4375274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4375274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4375274 prefixEnd_4375274 := by exact prefixLift 4375274
  have htrace : WordTrace (prefixWord ++ tailWord_4375274) baseStart_4375274 baseEnd_4375274 := by
    simpa [prefixWord, tailWord_4375274, baseEnd_4375274] using wordTrace_append hprefix tailTrace_4375274
  have hstable : (prefixWord ++ tailWord_4375274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4375274).length < 2 ^ (prefixWord ++ tailWord_4375274).sum := by decide
  have hdescent : baseEnd_4375274 < baseStart_4375274 := by decide
  rcases family_descends (prefixWord ++ tailWord_4375274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4375298 : List Nat := [3, 4, 1, 1, 1, 3, 1, 3, 1, 1, 4]
def baseStart_4375298 : Nat := 118140960795 + 4375298 * 2 ^ 59
def prefixEnd_4375298 : Nat := 4983230072969 + 3 ^ 40 * 4375298 * 2
def baseEnd_4375298 : Nat := 2246630880655527860153377

theorem tailTrace_4375298 : CollatzResearch.WordTrace tailWord_4375298 prefixEnd_4375298 2246630880655527860153377 := by
  unfold tailWord_4375298
  simp only [CollatzResearch.WordTrace]
  refine ⟨39895057025762515563145637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106386818735366708168388365 39895057025762515563145637)
  ·
    refine ⟨7480323192330471668089807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39895057025762515563145637 7480323192330471668089807)
    ·
      refine ⟨11220484788495707502134711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7480323192330471668089807 11220484788495707502134711)
      ·
        refine ⟨16830727182743561253202067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11220484788495707502134711 16830727182743561253202067)
        ·
          refine ⟨25246090774115341879803101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16830727182743561253202067 25246090774115341879803101)
          ·
            refine ⟨9467284040293253204926163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25246090774115341879803101 9467284040293253204926163)
            ·
              refine ⟨14200926060439879807389245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9467284040293253204926163 14200926060439879807389245)
              ·
                refine ⟨5325347272664954927770967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14200926060439879807389245 5325347272664954927770967)
                ·
                  refine ⟨7988020908997432391656451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5325347272664954927770967 7988020908997432391656451)
                  ·
                    refine ⟨11982031363496148587484677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7988020908997432391656451 11982031363496148587484677)
                    ·
                      refine ⟨2246630880655527860153377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11982031363496148587484677 2246630880655527860153377)
                      ·
                        rfl

theorem cell23_4375298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_4375298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4375298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4375298 prefixEnd_4375298 := by exact prefixLift 4375298
  have htrace : WordTrace (prefixWord ++ tailWord_4375298) baseStart_4375298 baseEnd_4375298 := by
    simpa [prefixWord, tailWord_4375298, baseEnd_4375298] using wordTrace_append hprefix tailTrace_4375298
  have hstable : (prefixWord ++ tailWord_4375298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4375298).length < 2 ^ (prefixWord ++ tailWord_4375298).sum := by decide
  have hdescent : baseEnd_4375298 < baseStart_4375298 := by decide
  rcases family_descends (prefixWord ++ tailWord_4375298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4375307 : List Nat := [1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 6]
def baseStart_4375307 : Nat := 118140960795 + 4375307 * 2 ^ 59
def prefixEnd_4375307 : Nat := 4983230072969 + 3 ^ 40 * 4375307 * 2
def baseEnd_4375307 : Nat := 2246635501981418324940835

theorem tailTrace_4375307 : CollatzResearch.WordTrace tailWord_4375307 prefixEnd_4375307 2246635501981418324940835 := by
  unfold tailWord_4375307
  simp only [CollatzResearch.WordTrace]
  refine ⟨159580556360017456789660175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106387037573344971193106783 159580556360017456789660175)
  ·
    refine ⟨239370834540026185184490263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159580556360017456789660175 239370834540026185184490263)
    ·
      refine ⟨359056251810039277776735395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239370834540026185184490263 359056251810039277776735395)
      ·
        refine ⟨538584377715058916665103093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 359056251810039277776735395 538584377715058916665103093)
        ·
          refine ⟨50492285410786773437353415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 538584377715058916665103093 50492285410786773437353415)
          ·
            refine ⟨75738428116180160156030123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50492285410786773437353415 75738428116180160156030123)
            ·
              refine ⟨113607642174270240234045185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75738428116180160156030123 113607642174270240234045185)
              ·
                refine ⟨85205731630702680175533889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113607642174270240234045185 85205731630702680175533889)
                ·
                  refine ⟨63904298723027010131650417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85205731630702680175533889 63904298723027010131650417)
                  ·
                    refine ⟨47928224042270257598737813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 63904298723027010131650417 47928224042270257598737813)
                    ·
                      refine ⟨2246635501981418324940835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47928224042270257598737813 2246635501981418324940835)
                      ·
                        rfl

theorem cell23_4375307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 6].length) (baseStart_4375307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4375307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4375307 prefixEnd_4375307 := by exact prefixLift 4375307
  have htrace : WordTrace (prefixWord ++ tailWord_4375307) baseStart_4375307 baseEnd_4375307 := by
    simpa [prefixWord, tailWord_4375307, baseEnd_4375307] using wordTrace_append hprefix tailTrace_4375307
  have hstable : (prefixWord ++ tailWord_4375307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4375307).length < 2 ^ (prefixWord ++ tailWord_4375307).sum := by decide
  have hdescent : baseEnd_4375307 < baseStart_4375307 := by decide
  rcases family_descends (prefixWord ++ tailWord_4375307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4375325 : List Nat := [1, 4, 2, 4, 2, 1, 1, 1, 1, 6]
def baseStart_4375325 : Nat := 118140960795 + 4375325 * 2 ^ 59
def prefixEnd_4375325 : Nat := 4983230072969 + 3 ^ 40 * 4375325 * 2
def baseEnd_4375325 : Nat := 748881581544399751505251

theorem tailTrace_4375325 : CollatzResearch.WordTrace tailWord_4375325 prefixEnd_4375325 748881581544399751505251 := by
  unfold tailWord_4375325
  simp only [CollatzResearch.WordTrace]
  refine ⟨159581212873952245863815429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106387475249301497242543619 159581212873952245863815429)
  ·
    refine ⟨29921477413866046099465393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 159581212873952245863815429 29921477413866046099465393)
    ·
      refine ⟨22441108060399534574599045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29921477413866046099465393 22441108060399534574599045)
      ·
        refine ⟨4207707761324912732737321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22441108060399534574599045 4207707761324912732737321)
        ·
          refine ⟨3155780820993684549552991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4207707761324912732737321 3155780820993684549552991)
          ·
            refine ⟨4733671231490526824329487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3155780820993684549552991 4733671231490526824329487)
            ·
              refine ⟨7100506847235790236494231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4733671231490526824329487 7100506847235790236494231)
              ·
                refine ⟨10650760270853685354741347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7100506847235790236494231 10650760270853685354741347)
                ·
                  refine ⟨15976140406280528032112021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10650760270853685354741347 15976140406280528032112021)
                  ·
                    refine ⟨748881581544399751505251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15976140406280528032112021 748881581544399751505251)
                    ·
                      rfl

theorem cell23_4375325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 1, 1, 6].length) (baseStart_4375325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4375325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4375325 prefixEnd_4375325 := by exact prefixLift 4375325
  have htrace : WordTrace (prefixWord ++ tailWord_4375325) baseStart_4375325 baseEnd_4375325 := by
    simpa [prefixWord, tailWord_4375325, baseEnd_4375325] using wordTrace_append hprefix tailTrace_4375325
  have hstable : (prefixWord ++ tailWord_4375325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4375325).length < 2 ^ (prefixWord ++ tailWord_4375325).sum := by decide
  have hdescent : baseEnd_4375325 < baseStart_4375325 := by decide
  rcases family_descends (prefixWord ++ tailWord_4375325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4375366 : List Nat := [6, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2]
def baseStart_4375366 : Nat := 118140960795 + 4375366 * 2 ^ 59
def prefixEnd_4375366 : Nat := 4983230072969 + 3 ^ 40 * 4375366 * 2
def baseEnd_4375366 : Nat := 2246665797340033594103065

theorem tailTrace_4375366 : CollatzResearch.WordTrace tailWord_4375366 prefixEnd_4375366 2246665797340033594103065 := by
  unfold tailWord_4375366
  simp only [CollatzResearch.WordTrace]
  refine ⟨4986959633337615933314311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 106388472177869139910705301 4986959633337615933314311)
  ·
    refine ⟨7480439450006423899971467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4986959633337615933314311 7480439450006423899971467)
    ·
      refine ⟨11220659175009635849957201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7480439450006423899971467 11220659175009635849957201)
      ·
        refine ⟨8415494381257226887467901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11220659175009635849957201 8415494381257226887467901)
        ·
          refine ⟨3155810392971460082800463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8415494381257226887467901 3155810392971460082800463)
          ·
            refine ⟨4733715589457190124200695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3155810392971460082800463 4733715589457190124200695)
            ·
              refine ⟨7100573384185785186301043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4733715589457190124200695 7100573384185785186301043)
              ·
                refine ⟨10650860076278677779451565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7100573384185785186301043 10650860076278677779451565)
                ·
                  refine ⟨3994072528604504167294337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10650860076278677779451565 3994072528604504167294337)
                  ·
                    refine ⟨2995554396453378125470753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3994072528604504167294337 2995554396453378125470753)
                    ·
                      refine ⟨2246665797340033594103065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2995554396453378125470753 2246665797340033594103065)
                      ·
                        rfl

theorem cell23_4375366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_4375366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4375366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4375366 prefixEnd_4375366 := by exact prefixLift 4375366
  have htrace : WordTrace (prefixWord ++ tailWord_4375366) baseStart_4375366 baseEnd_4375366 := by
    simpa [prefixWord, tailWord_4375366, baseEnd_4375366] using wordTrace_append hprefix tailTrace_4375366
  have hstable : (prefixWord ++ tailWord_4375366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4375366).length < 2 ^ (prefixWord ++ tailWord_4375366).sum := by decide
  have hdescent : baseEnd_4375366 < baseStart_4375366 := by decide
  rcases family_descends (prefixWord ++ tailWord_4375366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4375384 : List Nat := [2, 1, 2, 2, 1, 1, 1, 5, 2, 2, 4]
def baseStart_4375384 : Nat := 118140960795 + 4375384 * 2 ^ 59
def prefixEnd_4375384 : Nat := 4983230072969 + 3 ^ 40 * 4375384 * 2
def baseEnd_4375384 : Nat := 2246675039991814523677981

theorem tailTrace_4375384 : CollatzResearch.WordTrace tailWord_4375384 prefixEnd_4375384 2246675039991814523677981 := by
  unfold tailWord_4375384
  simp only [CollatzResearch.WordTrace]
  refine ⟨79791682390369249470106603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106388909853825665960142137 79791682390369249470106603)
  ·
    refine ⟨119687523585553874205159905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79791682390369249470106603 119687523585553874205159905)
    ·
      refine ⟨89765642689165405653869929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119687523585553874205159905 89765642689165405653869929)
      ·
        refine ⟨67324232016874054240402447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89765642689165405653869929 67324232016874054240402447)
        ·
          refine ⟨100986348025311081360603671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67324232016874054240402447 100986348025311081360603671)
          ·
            refine ⟨151479522037966622040905507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100986348025311081360603671 151479522037966622040905507)
            ·
              refine ⟨227219283056949933061358261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151479522037966622040905507 227219283056949933061358261)
              ·
                refine ⟨21301807786589056224502337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 227219283056949933061358261 21301807786589056224502337)
                ·
                  refine ⟨15976355839941792168376753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21301807786589056224502337 15976355839941792168376753)
                  ·
                    refine ⟨11982266879956344126282565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15976355839941792168376753 11982266879956344126282565)
                    ·
                      refine ⟨2246675039991814523677981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11982266879956344126282565 2246675039991814523677981)
                      ·
                        rfl

theorem cell23_4375384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 2, 2, 4].length) (baseStart_4375384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4375384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4375384 prefixEnd_4375384 := by exact prefixLift 4375384
  have htrace : WordTrace (prefixWord ++ tailWord_4375384) baseStart_4375384 baseEnd_4375384 := by
    simpa [prefixWord, tailWord_4375384, baseEnd_4375384] using wordTrace_append hprefix tailTrace_4375384
  have hstable : (prefixWord ++ tailWord_4375384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4375384).length < 2 ^ (prefixWord ++ tailWord_4375384).sum := by decide
  have hdescent : baseEnd_4375384 < baseStart_4375384 := by decide
  rcases family_descends (prefixWord ++ tailWord_4375384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4375424 : List Nat := [2, 1, 1, 2, 1, 2, 2, 3, 4, 5]
def baseStart_4375424 : Nat := 118140960795 + 4375424 * 2 ^ 59
def prefixEnd_4375424 : Nat := 4983230072969 + 3 ^ 40 * 4375424 * 2
def baseEnd_4375424 : Nat := 748898526405998122392599

theorem tailTrace_4375424 : CollatzResearch.WordTrace tailWord_4375424 prefixEnd_4375424 748898526405998122392599 := by
  unfold tailWord_4375424
  simp only [CollatzResearch.WordTrace]
  refine ⟨79792411850296792885834663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106389882467062390514446217 79792411850296792885834663)
  ·
    refine ⟨119688617775445189328751995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79792411850296792885834663 119688617775445189328751995)
    ·
      refine ⟨179532926663167783993127993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119688617775445189328751995 179532926663167783993127993)
      ·
        refine ⟨134649694997375837994845995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179532926663167783993127993 134649694997375837994845995)
        ·
          refine ⟨201974542496063756992268993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134649694997375837994845995 201974542496063756992268993)
          ·
            refine ⟨151480906872047817744201745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 201974542496063756992268993 151480906872047817744201745)
            ·
              refine ⟨113610680154035863308151309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 151480906872047817744201745 113610680154035863308151309)
              ·
                refine ⟨42604005057763448740556741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 113610680154035863308151309 42604005057763448740556741)
                ·
                  refine ⟨7988250948330646638854389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42604005057763448740556741 7988250948330646638854389)
                  ·
                    refine ⟨748898526405998122392599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7988250948330646638854389 748898526405998122392599)
                    ·
                      rfl

theorem cell23_4375424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 4, 5].length) (baseStart_4375424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4375424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4375424 prefixEnd_4375424 := by exact prefixLift 4375424
  have htrace : WordTrace (prefixWord ++ tailWord_4375424) baseStart_4375424 baseEnd_4375424 := by
    simpa [prefixWord, tailWord_4375424, baseEnd_4375424] using wordTrace_append hprefix tailTrace_4375424
  have hstable : (prefixWord ++ tailWord_4375424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4375424).length < 2 ^ (prefixWord ++ tailWord_4375424).sum := by decide
  have hdescent : baseEnd_4375424 < baseStart_4375424 := by decide
  rcases family_descends (prefixWord ++ tailWord_4375424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4375458 : List Nat := [3, 3, 1, 2, 2, 1, 3, 1, 2, 5]
def baseStart_4375458 : Nat := 118140960795 + 4375458 * 2 ^ 59
def prefixEnd_4375458 : Nat := 4983230072969 + 3 ^ 40 * 4375458 * 2
def baseEnd_4375458 : Nat := 748904345853415744717547

theorem tailTrace_4375458 : CollatzResearch.WordTrace tailWord_4375458 prefixEnd_4375458 748904345853415744717547 := by
  unfold tailWord_4375458
  simp only [CollatzResearch.WordTrace]
  refine ⟨39896515945617602394601757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106390709188313606385604685 39896515945617602394601757)
  ·
    refine ⟨14961193479606600897975659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39896515945617602394601757 14961193479606600897975659)
    ·
      refine ⟨22441790219409901346963489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14961193479606600897975659 22441790219409901346963489)
      ·
        refine ⟨16831342664557426010222617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22441790219409901346963489 16831342664557426010222617)
        ·
          refine ⟨12623506998418069507666963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16831342664557426010222617 12623506998418069507666963)
          ·
            refine ⟨18935260497627104261500445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12623506998418069507666963 18935260497627104261500445)
            ·
              refine ⟨7100722686610164098062667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18935260497627104261500445 7100722686610164098062667)
              ·
                refine ⟨10651084029915246147094001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7100722686610164098062667 10651084029915246147094001)
                ·
                  refine ⟨7988313022436434610320501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10651084029915246147094001 7988313022436434610320501)
                  ·
                    refine ⟨748904345853415744717547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7988313022436434610320501 748904345853415744717547)
                    ·
                      rfl

theorem cell23_4375458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 1, 2, 5].length) (baseStart_4375458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4375458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4375458 prefixEnd_4375458 := by exact prefixLift 4375458
  have htrace : WordTrace (prefixWord ++ tailWord_4375458) baseStart_4375458 baseEnd_4375458 := by
    simpa [prefixWord, tailWord_4375458, baseEnd_4375458] using wordTrace_append hprefix tailTrace_4375458
  have hstable : (prefixWord ++ tailWord_4375458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4375458).length < 2 ^ (prefixWord ++ tailWord_4375458).sum := by decide
  have hdescent : baseEnd_4375458 < baseStart_4375458 := by decide
  rcases family_descends (prefixWord ++ tailWord_4375458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4375488 : List Nat := [2, 1, 1, 2, 3, 4, 2, 1, 3, 4]
def baseStart_4375488 : Nat := 118140960795 + 4375488 * 2 ^ 59
def prefixEnd_4375488 : Nat := 4983230072969 + 3 ^ 40 * 4375488 * 2
def baseEnd_4375488 : Nat := 748909480659960705592501

theorem tailTrace_4375488 : CollatzResearch.WordTrace tailWord_4375488 prefixEnd_4375488 748909480659960705592501 := by
  unfold tailWord_4375488
  simp only [CollatzResearch.WordTrace]
  refine ⟨79793578986180862350999559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106391438648241149801332745 79793578986180862350999559)
  ·
    refine ⟨119690368479271293526499339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79793578986180862350999559 119690368479271293526499339)
    ·
      refine ⟨179535552718906940289749009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119690368479271293526499339 179535552718906940289749009)
      ·
        refine ⟨134651664539180205217311757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179535552718906940289749009 134651664539180205217311757)
        ·
          refine ⟨50494374202192576956491909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134651664539180205217311757 50494374202192576956491909)
          ·
            refine ⟨9467695162911108179342233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50494374202192576956491909 9467695162911108179342233)
            ·
              refine ⟨7100771372183331134506675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9467695162911108179342233 7100771372183331134506675)
              ·
                refine ⟨10651157058274996701760013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7100771372183331134506675 10651157058274996701760013)
                ·
                  refine ⟨3994183896853123763160005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10651157058274996701760013 3994183896853123763160005)
                  ·
                    refine ⟨748909480659960705592501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3994183896853123763160005 748909480659960705592501)
                    ·
                      rfl

theorem cell23_4375488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 1, 3, 4].length) (baseStart_4375488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4375488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4375488 prefixEnd_4375488 := by exact prefixLift 4375488
  have htrace : WordTrace (prefixWord ++ tailWord_4375488) baseStart_4375488 baseEnd_4375488 := by
    simpa [prefixWord, tailWord_4375488, baseEnd_4375488] using wordTrace_append hprefix tailTrace_4375488
  have hstable : (prefixWord ++ tailWord_4375488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4375488).length < 2 ^ (prefixWord ++ tailWord_4375488).sum := by decide
  have hdescent : baseEnd_4375488 < baseStart_4375488 := by decide
  rcases family_descends (prefixWord ++ tailWord_4375488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4375504 : List Nat := [2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 6]
def baseStart_4375504 : Nat := 118140960795 + 4375504 * 2 ^ 59
def prefixEnd_4375504 : Nat := 4983230072969 + 3 ^ 40 * 4375504 * 2
def baseEnd_4375504 : Nat := 2246736657670354054177429

theorem tailTrace_4375504 : CollatzResearch.WordTrace tailWord_4375504 prefixEnd_4375504 2246736657670354054177429 := by
  unfold tailWord_4375504
  simp only [CollatzResearch.WordTrace]
  refine ⟨79793870770151879717290783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106391827693535839623054377 79793870770151879717290783)
  ·
    refine ⟨119690806155227819575936175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79793870770151879717290783 119690806155227819575936175)
    ·
      refine ⟨179536209232841729363904263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119690806155227819575936175 179536209232841729363904263)
      ·
        refine ⟨269304313849262594045856395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179536209232841729363904263 269304313849262594045856395)
        ·
          refine ⟨403956470773893891068784593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 269304313849262594045856395 403956470773893891068784593)
          ·
            refine ⟨302967353080420418301588445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 403956470773893891068784593 302967353080420418301588445)
            ·
              refine ⟨113612757405157656863095667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 302967353080420418301588445 113612757405157656863095667)
              ·
                refine ⟨170419136107736485294643501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113612757405157656863095667 170419136107736485294643501)
                ·
                  refine ⟨63907176040401181985491313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 170419136107736485294643501 63907176040401181985491313)
                  ·
                    refine ⟨47930382030300886489118485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 63907176040401181985491313 47930382030300886489118485)
                    ·
                      refine ⟨2246736657670354054177429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47930382030300886489118485 2246736657670354054177429)
                      ·
                        rfl

theorem cell23_4375504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 6].length) (baseStart_4375504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4375504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4375504 prefixEnd_4375504 := by exact prefixLift 4375504
  have htrace : WordTrace (prefixWord ++ tailWord_4375504) baseStart_4375504 baseEnd_4375504 := by
    simpa [prefixWord, tailWord_4375504, baseEnd_4375504] using wordTrace_append hprefix tailTrace_4375504
  have hstable : (prefixWord ++ tailWord_4375504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4375504).length < 2 ^ (prefixWord ++ tailWord_4375504).sum := by decide
  have hdescent : baseEnd_4375504 < baseStart_4375504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4375504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4375528 : List Nat := [2, 1, 4, 1, 1, 1, 2, 2, 5, 1, 3]
def baseStart_4375528 : Nat := 118140960795 + 4375528 * 2 ^ 59
def prefixEnd_4375528 : Nat := 4983230072969 + 3 ^ 40 * 4375528 * 2
def baseEnd_4375528 : Nat := 2246748981206061960277319

theorem tailTrace_4375528 : CollatzResearch.WordTrace tailWord_4375528 prefixEnd_4375528 2246748981206061960277319 := by
  unfold tailWord_4375528
  simp only [CollatzResearch.WordTrace]
  refine ⟨79794308446108405766727619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106392411261477874355636825 79794308446108405766727619)
  ·
    refine ⟨119691462669162608650091429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79794308446108405766727619 119691462669162608650091429)
    ·
      refine ⟨22442149250467989121892143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 119691462669162608650091429 22442149250467989121892143)
      ·
        refine ⟨33663223875701983682838215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22442149250467989121892143 33663223875701983682838215)
        ·
          refine ⟨50494835813552975524257323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33663223875701983682838215 50494835813552975524257323)
          ·
            refine ⟨75742253720329463286385985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50494835813552975524257323 75742253720329463286385985)
            ·
              refine ⟨56806690290247097464789489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75742253720329463286385985 56806690290247097464789489)
              ·
                refine ⟨42605017717685323098592117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56806690290247097464789489 42605017717685323098592117)
                ·
                  refine ⟨3994220411032999040493011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42605017717685323098592117 3994220411032999040493011)
                  ·
                    refine ⟨5991330616549498560739517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3994220411032999040493011 5991330616549498560739517)
                    ·
                      refine ⟨2246748981206061960277319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5991330616549498560739517 2246748981206061960277319)
                      ·
                        rfl

theorem cell23_4375528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 5, 1, 3].length) (baseStart_4375528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4375528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4375528 prefixEnd_4375528 := by exact prefixLift 4375528
  have htrace : WordTrace (prefixWord ++ tailWord_4375528) baseStart_4375528 baseEnd_4375528 := by
    simpa [prefixWord, tailWord_4375528, baseEnd_4375528] using wordTrace_append hprefix tailTrace_4375528
  have hstable : (prefixWord ++ tailWord_4375528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4375528).length < 2 ^ (prefixWord ++ tailWord_4375528).sum := by decide
  have hdescent : baseEnd_4375528 < baseStart_4375528 := by decide
  rcases family_descends (prefixWord ++ tailWord_4375528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4375598 : List Nat := [4, 1, 3, 1, 1, 1, 1, 2, 3, 2, 4]
def baseStart_4375598 : Nat := 118140960795 + 4375598 * 2 ^ 59
def prefixEnd_4375598 : Nat := 4983230072969 + 3 ^ 40 * 4375598 * 2
def baseEnd_4375598 : Nat := 2246784924851876686401997

theorem tailTrace_4375598 : CollatzResearch.WordTrace tailWord_4375598 prefixEnd_4375598 2246784924851876686401997 := by
  unfold tailWord_4375598
  simp only [CollatzResearch.WordTrace]
  refine ⟨19948896250245401686062931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106394113334642142325668965 19948896250245401686062931)
  ·
    refine ⟨29923344375368102529094397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19948896250245401686062931 29923344375368102529094397)
    ·
      refine ⟨11221254140763038448410399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29923344375368102529094397 11221254140763038448410399)
      ·
        refine ⟨16831881211144557672615599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11221254140763038448410399 16831881211144557672615599)
        ·
          refine ⟨25247821816716836508923399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16831881211144557672615599 25247821816716836508923399)
          ·
            refine ⟨37871732725075254763385099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25247821816716836508923399 37871732725075254763385099)
            ·
              refine ⟨56807599087612882145077649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37871732725075254763385099 56807599087612882145077649)
              ·
                refine ⟨42605699315709661608808237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56807599087612882145077649 42605699315709661608808237)
                ·
                  refine ⟨15977137243391123103303089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42605699315709661608808237 15977137243391123103303089)
                  ·
                    refine ⟨11982852932543342327477317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15977137243391123103303089 11982852932543342327477317)
                    ·
                      refine ⟨2246784924851876686401997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11982852932543342327477317 2246784924851876686401997)
                      ·
                        rfl

theorem cell23_4375598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_4375598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4375598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4375598 prefixEnd_4375598 := by exact prefixLift 4375598
  have htrace : WordTrace (prefixWord ++ tailWord_4375598) baseStart_4375598 baseEnd_4375598 := by
    simpa [prefixWord, tailWord_4375598, baseEnd_4375598] using wordTrace_append hprefix tailTrace_4375598
  have hstable : (prefixWord ++ tailWord_4375598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4375598).length < 2 ^ (prefixWord ++ tailWord_4375598).sum := by decide
  have hdescent : baseEnd_4375598 < baseStart_4375598 := by decide
  rcases family_descends (prefixWord ++ tailWord_4375598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4375608 : List Nat := [2, 1, 2, 1, 5, 3, 1, 8]
def baseStart_4375608 : Nat := 118140960795 + 4375608 * 2 ^ 59
def prefixEnd_4375608 : Nat := 4983230072969 + 3 ^ 40 * 4375608 * 2
def baseEnd_4375608 : Nat := 83214446654015616565813

theorem tailTrace_4375608 : CollatzResearch.WordTrace tailWord_4375608 prefixEnd_4375608 83214446654015616565813 := by
  unfold tailWord_4375608
  simp only [CollatzResearch.WordTrace]
  refine ⟨79795767365963492598183739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106394356487951323464244985 79795767365963492598183739)
  ·
    refine ⟨119693651048945238897275609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79795767365963492598183739 119693651048945238897275609)
    ·
      refine ⟨89770238286708929172956707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119693651048945238897275609 89770238286708929172956707)
      ·
        refine ⟨134655357430063393759435061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89770238286708929172956707 134655357430063393759435061)
        ·
          refine ⟨12623939759068443164947037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 134655357430063393759435061 12623939759068443164947037)
          ·
            refine ⟨4733977409650666186855139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12623939759068443164947037 4733977409650666186855139)
            ·
              refine ⟨7100966114475999280282709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4733977409650666186855139 7100966114475999280282709)
              ·
                refine ⟨83214446654015616565813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7100966114475999280282709 83214446654015616565813)
                ·
                  rfl

theorem cell23_4375608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 8].length) (baseStart_4375608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4375608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4375608 prefixEnd_4375608 := by exact prefixLift 4375608
  have htrace : WordTrace (prefixWord ++ tailWord_4375608) baseStart_4375608 baseEnd_4375608 := by
    simpa [prefixWord, tailWord_4375608, baseEnd_4375608] using wordTrace_append hprefix tailTrace_4375608
  have hstable : (prefixWord ++ tailWord_4375608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4375608).length < 2 ^ (prefixWord ++ tailWord_4375608).sum := by decide
  have hdescent : baseEnd_4375608 < baseStart_4375608 := by decide
  rcases family_descends (prefixWord ++ tailWord_4375608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4375622 : List Nat := [6, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3]
def baseStart_4375622 : Nat := 118140960795 + 4375622 * 2 ^ 59
def prefixEnd_4375622 : Nat := 4983230072969 + 3 ^ 40 * 4375622 * 2
def baseEnd_4375622 : Nat := 2246797248387584592501887

theorem tailTrace_4375622 : CollatzResearch.WordTrace tailWord_4375622 prefixEnd_4375622 2246797248387584592501887 := by
  unfold tailWord_4375622
  simp only [CollatzResearch.WordTrace]
  refine ⟨4987251417308633299605535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 106394696902584177058251413 4987251417308633299605535)
  ·
    refine ⟨7480877125962949949408303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4987251417308633299605535 7480877125962949949408303)
    ·
      refine ⟨11221315688944424924112455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7480877125962949949408303 11221315688944424924112455)
      ·
        refine ⟨16831973533416637386168683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11221315688944424924112455 16831973533416637386168683)
        ·
          refine ⟨25247960300124956079253025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16831973533416637386168683 25247960300124956079253025)
          ·
            refine ⟨18935970225093717059439769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25247960300124956079253025 18935970225093717059439769)
            ·
              refine ⟨14201977668820287794579827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18935970225093717059439769 14201977668820287794579827)
              ·
                refine ⟨21302966503230431691869741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14201977668820287794579827 21302966503230431691869741)
                ·
                  refine ⟨7988612438711411884451153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21302966503230431691869741 7988612438711411884451153)
                  ·
                    refine ⟨5991459329033558913338365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7988612438711411884451153 5991459329033558913338365)
                    ·
                      refine ⟨2246797248387584592501887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5991459329033558913338365 2246797248387584592501887)
                      ·
                        rfl

theorem cell23_4375622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_4375622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4375622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4375622 prefixEnd_4375622 := by exact prefixLift 4375622
  have htrace : WordTrace (prefixWord ++ tailWord_4375622) baseStart_4375622 baseEnd_4375622 := by
    simpa [prefixWord, tailWord_4375622, baseEnd_4375622] using wordTrace_append hprefix tailTrace_4375622
  have hstable : (prefixWord ++ tailWord_4375622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4375622).length < 2 ^ (prefixWord ++ tailWord_4375622).sum := by decide
  have hdescent : baseEnd_4375622 < baseStart_4375622 := by decide
  rcases family_descends (prefixWord ++ tailWord_4375622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4375641 : List Nat := [1, 2, 1, 2, 2, 1, 2, 2, 1, 5, 4]
def baseStart_4375641 : Nat := 118140960795 + 4375641 * 2 ^ 59
def prefixEnd_4375641 : Nat := 4983230072969 + 3 ^ 40 * 4375641 * 2
def baseEnd_4375641 : Nat := 2246807004520020018164299

theorem tailTrace_4375641 : CollatzResearch.WordTrace tailWord_4375641 prefixEnd_4375641 2246807004520020018164299 := by
  unfold tailWord_4375641
  simp only [CollatzResearch.WordTrace]
  refine ⟨159592738340807431832318777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106395158893871621221545851 159592738340807431832318777)
  ·
    refine ⟨119694553755605573874239083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159592738340807431832318777 119694553755605573874239083)
    ·
      refine ⟨179541830633408360811358625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119694553755605573874239083 179541830633408360811358625)
      ·
        refine ⟨134656372975056270608518969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179541830633408360811358625 134656372975056270608518969)
        ·
          refine ⟨100992279731292202956389227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134656372975056270608518969 100992279731292202956389227)
          ·
            refine ⟨151488419596938304434583841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100992279731292202956389227 151488419596938304434583841)
            ·
              refine ⟨113616314697703728325937881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 151488419596938304434583841 113616314697703728325937881)
              ·
                refine ⟨85212236023277796244453411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113616314697703728325937881 85212236023277796244453411)
                ·
                  refine ⟨127818354034916694366680117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85212236023277796244453411 127818354034916694366680117)
                  ·
                    refine ⟨11982970690773440096876261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 127818354034916694366680117 11982970690773440096876261)
                    ·
                      refine ⟨2246807004520020018164299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11982970690773440096876261 2246807004520020018164299)
                      ·
                        rfl

theorem cell23_4375641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 5, 4].length) (baseStart_4375641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4375641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4375641 prefixEnd_4375641 := by exact prefixLift 4375641
  have htrace : WordTrace (prefixWord ++ tailWord_4375641) baseStart_4375641 baseEnd_4375641 := by
    simpa [prefixWord, tailWord_4375641, baseEnd_4375641] using wordTrace_append hprefix tailTrace_4375641
  have hstable : (prefixWord ++ tailWord_4375641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4375641).length < 2 ^ (prefixWord ++ tailWord_4375641).sum := by decide
  have hdescent : baseEnd_4375641 < baseStart_4375641 := by decide
  rcases family_descends (prefixWord ++ tailWord_4375641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4375646 : List Nat := [4, 4, 1, 1, 1, 3, 1, 2, 2, 4]
def baseStart_4375646 : Nat := 118140960795 + 4375646 * 2 ^ 59
def prefixEnd_4375646 : Nat := 4983230072969 + 3 ^ 40 * 4375646 * 2
def baseEnd_4375646 : Nat := 748936523974430832867259

theorem tailTrace_4375646 : CollatzResearch.WordTrace tailWord_4375646 prefixEnd_4375646 748936523974430832867259 := by
  unfold tailWord_4375646
  simp only [CollatzResearch.WordTrace]
  refine ⟨19949115088223664710781349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106395280470526211790833861 19949115088223664710781349)
  ·
    refine ⟨3740459079041937133271503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19949115088223664710781349 3740459079041937133271503)
    ·
      refine ⟨5610688618562905699907255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3740459079041937133271503 5610688618562905699907255)
      ·
        refine ⟨8416032927844358549860883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5610688618562905699907255 8416032927844358549860883)
        ·
          refine ⟨12624049391766537824791325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8416032927844358549860883 12624049391766537824791325)
          ·
            refine ⟨4734018521912451684296747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12624049391766537824791325 4734018521912451684296747)
            ·
              refine ⟨7101027782868677526445121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4734018521912451684296747 7101027782868677526445121)
              ·
                refine ⟨5325770837151508144833841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7101027782868677526445121 5325770837151508144833841)
                ·
                  refine ⟨3994328127863631108625381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5325770837151508144833841 3994328127863631108625381)
                  ·
                    refine ⟨748936523974430832867259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3994328127863631108625381 748936523974430832867259)
                    ·
                      rfl

theorem cell23_4375646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_4375646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4375646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4375646 prefixEnd_4375646 := by exact prefixLift 4375646
  have htrace : WordTrace (prefixWord ++ tailWord_4375646) baseStart_4375646 baseEnd_4375646 := by
    simpa [prefixWord, tailWord_4375646, baseEnd_4375646] using wordTrace_append hprefix tailTrace_4375646
  have hstable : (prefixWord ++ tailWord_4375646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4375646).length < 2 ^ (prefixWord ++ tailWord_4375646).sum := by decide
  have hdescent : baseEnd_4375646 < baseStart_4375646 := by decide
  rcases family_descends (prefixWord ++ tailWord_4375646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4375669 : List Nat := [1, 3, 4, 3, 1, 2, 1, 1, 1, 3, 3]
def baseStart_4375669 : Nat := 118140960795 + 4375669 * 2 ^ 59
def prefixEnd_4375669 : Nat := 4983230072969 + 3 ^ 40 * 4375669 * 2
def baseEnd_4375669 : Nat := 2246821381978345908614171

theorem tailTrace_4375669 : CollatzResearch.WordTrace tailWord_4375669 prefixEnd_4375669 2246821381978345908614171 := by
  unfold tailWord_4375669
  simp only [CollatzResearch.WordTrace]
  refine ⟨159593759584705992614338061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106395839723137328409558707 159593759584705992614338061)
  ·
    refine ⟨59847659844264747230376773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159593759584705992614338061 59847659844264747230376773)
    ·
      refine ⟨11221436220799640105695645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59847659844264747230376773 11221436220799640105695645)
      ·
        refine ⟨4208038582799865039635867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11221436220799640105695645 4208038582799865039635867)
        ·
          refine ⟨6312057874199797559453801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4208038582799865039635867 6312057874199797559453801)
          ·
            refine ⟨4734043405649848169590351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6312057874199797559453801 4734043405649848169590351)
            ·
              refine ⟨7101065108474772254385527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4734043405649848169590351 7101065108474772254385527)
              ·
                refine ⟨10651597662712158381578291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7101065108474772254385527 10651597662712158381578291)
                ·
                  refine ⟨15977396494068237572367437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10651597662712158381578291 15977396494068237572367437)
                  ·
                    refine ⟨5991523685275589089637789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15977396494068237572367437 5991523685275589089637789)
                    ·
                      refine ⟨2246821381978345908614171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5991523685275589089637789 2246821381978345908614171)
                      ·
                        rfl

theorem cell23_4375669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_4375669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4375669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4375669 prefixEnd_4375669 := by exact prefixLift 4375669
  have htrace : WordTrace (prefixWord ++ tailWord_4375669) baseStart_4375669 baseEnd_4375669 := by
    simpa [prefixWord, tailWord_4375669, baseEnd_4375669] using wordTrace_append hprefix tailTrace_4375669
  have hstable : (prefixWord ++ tailWord_4375669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4375669).length < 2 ^ (prefixWord ++ tailWord_4375669).sum := by decide
  have hdescent : baseEnd_4375669 < baseStart_4375669 := by decide
  rcases family_descends (prefixWord ++ tailWord_4375669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4375809 : List Nat := [1, 2, 4, 1, 1, 4, 2, 3, 1, 4]
def baseStart_4375809 : Nat := 118140960795 + 4375809 * 2 ^ 59
def prefixEnd_4375809 : Nat := 4983230072969 + 3 ^ 40 * 4375809 * 2
def baseEnd_4375809 : Nat := 748964423089991786954509

theorem tailTrace_4375809 : CollatzResearch.WordTrace tailWord_4375809 prefixEnd_4375809 748964423089991786954509 := by
  unfold tailWord_4375809
  simp only [CollatzResearch.WordTrace]
  refine ⟨159598865804198796524434481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106399243869465864349622987 159598865804198796524434481)
  ·
    refine ⟨119699149353149097393325861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159598865804198796524434481 119699149353149097393325861)
    ·
      refine ⟨22443590503715455761248599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 119699149353149097393325861 22443590503715455761248599)
      ·
        refine ⟨33665385755573183641872899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22443590503715455761248599 33665385755573183641872899)
        ·
          refine ⟨50498078633359775462809349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33665385755573183641872899 50498078633359775462809349)
          ·
            refine ⟨9468389743754957899276753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50498078633359775462809349 9468389743754957899276753)
            ·
              refine ⟨7101292307816218424457565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9468389743754957899276753 7101292307816218424457565)
              ·
                refine ⟨2662984615431081909171587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7101292307816218424457565 2662984615431081909171587)
                ·
                  refine ⟨3994476923146622863757381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2662984615431081909171587 3994476923146622863757381)
                  ·
                    refine ⟨748964423089991786954509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3994476923146622863757381 748964423089991786954509)
                    ·
                      rfl

theorem cell23_4375809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 3, 1, 4].length) (baseStart_4375809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4375809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4375809 prefixEnd_4375809 := by exact prefixLift 4375809
  have htrace : WordTrace (prefixWord ++ tailWord_4375809) baseStart_4375809 baseEnd_4375809 := by
    simpa [prefixWord, tailWord_4375809, baseEnd_4375809] using wordTrace_append hprefix tailTrace_4375809
  have hstable : (prefixWord ++ tailWord_4375809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4375809).length < 2 ^ (prefixWord ++ tailWord_4375809).sum := by decide
  have hdescent : baseEnd_4375809 < baseStart_4375809 := by decide
  rcases family_descends (prefixWord ++ tailWord_4375809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4375822 : List Nat := [4, 1, 1, 2, 1, 5, 1, 2, 6]
def baseStart_4375822 : Nat := 118140960795 + 4375822 * 2 ^ 59
def prefixEnd_4375822 : Nat := 4983230072969 + 3 ^ 40 * 4375822 * 2
def baseEnd_4375822 : Nat := 249655549390942645555663

theorem tailTrace_4375822 : CollatzResearch.WordTrace tailWord_4375822 prefixEnd_4375822 249655549390942645555663 := by
  unfold tailWord_4375822
  simp only [CollatzResearch.WordTrace]
  refine ⟨19949917494143962468082215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106399559968767799829771813 19949917494143962468082215)
  ·
    refine ⟨29924876241215943702123323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19949917494143962468082215 29924876241215943702123323)
    ·
      refine ⟨44887314361823915553184985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29924876241215943702123323 44887314361823915553184985)
      ·
        refine ⟨33665485771367936664888739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44887314361823915553184985 33665485771367936664888739)
        ·
          refine ⟨50498228657051904997333109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33665485771367936664888739 50498228657051904997333109)
          ·
            refine ⟨4734208936598616093499979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50498228657051904997333109 4734208936598616093499979)
            ·
              refine ⟨7101313404897924140249969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4734208936598616093499979 7101313404897924140249969)
              ·
                refine ⟨5325985053673443105187477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7101313404897924140249969 5325985053673443105187477)
                ·
                  refine ⟨249655549390942645555663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5325985053673443105187477 249655549390942645555663)
                  ·
                    rfl

theorem cell23_4375822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 2, 6].length) (baseStart_4375822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4375822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4375822 prefixEnd_4375822 := by exact prefixLift 4375822
  have htrace : WordTrace (prefixWord ++ tailWord_4375822) baseStart_4375822 baseEnd_4375822 := by
    simpa [prefixWord, tailWord_4375822, baseEnd_4375822] using wordTrace_append hprefix tailTrace_4375822
  have hstable : (prefixWord ++ tailWord_4375822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4375822).length < 2 ^ (prefixWord ++ tailWord_4375822).sum := by decide
  have hdescent : baseEnd_4375822 < baseStart_4375822 := by decide
  rcases family_descends (prefixWord ++ tailWord_4375822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4375826 : List Nat := [3, 2, 4, 2, 1, 1, 2, 1, 3, 4]
def baseStart_4375826 : Nat := 118140960795 + 4375826 * 2 ^ 59
def prefixEnd_4375826 : Nat := 4983230072969 + 3 ^ 40 * 4375826 * 2
def baseEnd_4375826 : Nat := 748967332813700598116983

theorem tailTrace_4375826 : CollatzResearch.WordTrace tailWord_4375826 prefixEnd_4375826 748967332813700598116983 := by
  unfold tailWord_4375826
  simp only [CollatzResearch.WordTrace]
  refine ⟨39899871461284302106950833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106399657230091472285202221 39899871461284302106950833)
  ·
    refine ⟨29924903595963226580213125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39899871461284302106950833 29924903595963226580213125)
    ·
      refine ⟨5610919424243104983789961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29924903595963226580213125 5610919424243104983789961)
      ·
        refine ⟨4208189568182328737842471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5610919424243104983789961 4208189568182328737842471)
        ·
          refine ⟨6312284352273493106763707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4208189568182328737842471 6312284352273493106763707)
          ·
            refine ⟨9468426528410239660145561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6312284352273493106763707 9468426528410239660145561)
            ·
              refine ⟨7101319896307679745109171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9468426528410239660145561 7101319896307679745109171)
              ·
                refine ⟨10651979844461519617663757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7101319896307679745109171 10651979844461519617663757)
                ·
                  refine ⟨3994492441673069856623909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10651979844461519617663757 3994492441673069856623909)
                  ·
                    refine ⟨748967332813700598116983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3994492441673069856623909 748967332813700598116983)
                    ·
                      rfl

theorem cell23_4375826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_4375826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4375826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4375826 prefixEnd_4375826 := by exact prefixLift 4375826
  have htrace : WordTrace (prefixWord ++ tailWord_4375826) baseStart_4375826 baseEnd_4375826 := by
    simpa [prefixWord, tailWord_4375826, baseEnd_4375826] using wordTrace_append hprefix tailTrace_4375826
  have hstable : (prefixWord ++ tailWord_4375826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4375826).length < 2 ^ (prefixWord ++ tailWord_4375826).sum := by decide
  have hdescent : baseEnd_4375826 < baseStart_4375826 := by decide
  rcases family_descends (prefixWord ++ tailWord_4375826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4375832 : List Nat := [2, 1, 2, 3, 1, 3, 1, 3, 3, 1, 3]
def baseStart_4375832 : Nat := 118140960795 + 4375832 * 2 ^ 59
def prefixEnd_4375832 : Nat := 4983230072969 + 3 ^ 40 * 4375832 * 2
def baseEnd_4375832 : Nat := 2246905079325028770875921

theorem tailTrace_4375832 : CollatzResearch.WordTrace tailWord_4375832 prefixEnd_4375832 2246905079325028770875921 := by
  unfold tailWord_4375832
  simp only [CollatzResearch.WordTrace]
  refine ⟨79799852341557735726260875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106399803122076980968347833 79799852341557735726260875)
  ·
    refine ⟨119699778512336603589391313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79799852341557735726260875 119699778512336603589391313)
    ·
      refine ⟨89774833884252452692043485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119699778512336603589391313 89774833884252452692043485)
      ·
        refine ⟨33665562706594669759516307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89774833884252452692043485 33665562706594669759516307)
        ·
          refine ⟨50498344059892004639274461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33665562706594669759516307 50498344059892004639274461)
          ·
            refine ⟨18936879022459501739727923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50498344059892004639274461 18936879022459501739727923)
            ·
              refine ⟨28405318533689252609591885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18936879022459501739727923 28405318533689252609591885)
              ·
                refine ⟨10651994450133469728596957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28405318533689252609591885 10651994450133469728596957)
                ·
                  refine ⟨3994497918800051148223859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10651994450133469728596957 3994497918800051148223859)
                  ·
                    refine ⟨5991746878200076722335789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3994497918800051148223859 5991746878200076722335789)
                    ·
                      refine ⟨2246905079325028770875921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5991746878200076722335789 2246905079325028770875921)
                      ·
                        rfl

theorem cell23_4375832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 3, 3, 1, 3].length) (baseStart_4375832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4375832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4375832 prefixEnd_4375832 := by exact prefixLift 4375832
  have htrace : WordTrace (prefixWord ++ tailWord_4375832) baseStart_4375832 baseEnd_4375832 := by
    simpa [prefixWord, tailWord_4375832, baseEnd_4375832] using wordTrace_append hprefix tailTrace_4375832
  have hstable : (prefixWord ++ tailWord_4375832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4375832).length < 2 ^ (prefixWord ++ tailWord_4375832).sum := by decide
  have hdescent : baseEnd_4375832 < baseStart_4375832 := by decide
  rcases family_descends (prefixWord ++ tailWord_4375832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
