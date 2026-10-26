import V185TrunkScan23Chunk0881

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5220030 : List Nat := [4, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3]
def baseStart_5220030 : Nat := 118140960795 + 5220030 * 2 ^ 59
def prefixEnd_5220030 : Nat := 4983230072969 + 3 ^ 40 * 5220030 * 2
def baseEnd_5220030 : Nat := 2680384420889316842318525

theorem tailTrace_5220030 : CollatzResearch.WordTrace tailWord_5220030 prefixEnd_5220030 2680384420889316842318525 := by
  unfold tailWord_5220030
  simp only [CollatzResearch.WordTrace]
  refine ⟨23798766909841286874045193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126926756852486863328241029 23798766909841286874045193)
  ·
    refine ⟨17849075182380965155533895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23798766909841286874045193 17849075182380965155533895)
    ·
      refine ⟨26773612773571447733300843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17849075182380965155533895 26773612773571447733300843)
      ·
        refine ⟨40160419160357171599951265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26773612773571447733300843 40160419160357171599951265)
        ·
          refine ⟨30120314370267878699963449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40160419160357171599951265 30120314370267878699963449)
          ·
            refine ⟨22590235777700909024972587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30120314370267878699963449 22590235777700909024972587)
            ·
              refine ⟨33885353666551363537458881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22590235777700909024972587 33885353666551363537458881)
              ·
                refine ⟨25414015249913522653094161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33885353666551363537458881 25414015249913522653094161)
                ·
                  refine ⟨19060511437435141989820621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25414015249913522653094161 19060511437435141989820621)
                  ·
                    refine ⟨7147691789038178246182733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19060511437435141989820621 7147691789038178246182733)
                    ·
                      refine ⟨2680384420889316842318525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7147691789038178246182733 2680384420889316842318525)
                      ·
                        rfl

theorem cell23_5220030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3].length) (baseStart_5220030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5220030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5220030 prefixEnd_5220030 := by exact prefixLift 5220030
  have htrace : WordTrace (prefixWord ++ tailWord_5220030) baseStart_5220030 baseEnd_5220030 := by
    simpa [prefixWord, tailWord_5220030, baseEnd_5220030] using wordTrace_append hprefix tailTrace_5220030
  have hstable : (prefixWord ++ tailWord_5220030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5220030).length < 2 ^ (prefixWord ++ tailWord_5220030).sum := by decide
  have hdescent : baseEnd_5220030 < baseStart_5220030 := by decide
  rcases family_descends (prefixWord ++ tailWord_5220030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5220071 : List Nat := [1, 1, 5, 4, 2, 1, 1, 3, 5]
def baseStart_5220071 : Nat := 118140960795 + 5220071 * 2 ^ 59
def prefixEnd_5220071 : Nat := 4983230072969 + 3 ^ 40 * 5220071 * 2
def baseEnd_5220071 : Nat := 297822830399572353545093

theorem tailTrace_5220071 : CollatzResearch.WordTrace tailWord_5220071 prefixEnd_5220071 297822830399572353545093 := by
  unfold tailWord_5220071
  simp only [CollatzResearch.WordTrace]
  refine ⟨190391630671581758994604067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126927753781054505996402711 190391630671581758994604067)
  ·
    refine ⟨285587446007372638491906101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190391630671581758994604067 285587446007372638491906101)
    ·
      refine ⟨26773823063191184858616197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 285587446007372638491906101 26773823063191184858616197)
      ·
        refine ⟨5020091824348347160990537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26773823063191184858616197 5020091824348347160990537)
        ·
          refine ⟨3765068868261260370742903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5020091824348347160990537 3765068868261260370742903)
          ·
            refine ⟨5647603302391890556114355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3765068868261260370742903 5647603302391890556114355)
            ·
              refine ⟨8471404953587835834171533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5647603302391890556114355 8471404953587835834171533)
              ·
                refine ⟨3176776857595438437814325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8471404953587835834171533 3176776857595438437814325)
                ·
                  refine ⟨297822830399572353545093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3176776857595438437814325 297822830399572353545093)
                  ·
                    rfl

theorem cell23_5220071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 3, 5].length) (baseStart_5220071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5220071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5220071 prefixEnd_5220071 := by exact prefixLift 5220071
  have htrace : WordTrace (prefixWord ++ tailWord_5220071) baseStart_5220071 baseEnd_5220071 := by
    simpa [prefixWord, tailWord_5220071, baseEnd_5220071] using wordTrace_append hprefix tailTrace_5220071
  have hstable : (prefixWord ++ tailWord_5220071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5220071).length < 2 ^ (prefixWord ++ tailWord_5220071).sum := by decide
  have hdescent : baseEnd_5220071 < baseStart_5220071 := by decide
  rcases family_descends (prefixWord ++ tailWord_5220071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5220084 : List Nat := [2, 6, 1, 1, 1, 2, 1, 2, 2, 5]
def baseStart_5220084 : Nat := 118140960795 + 5220084 * 2 ^ 59
def prefixEnd_5220084 : Nat := 4983230072969 + 3 ^ 40 * 5220084 * 2
def baseEnd_5220084 : Nat := 893470716281553210347759

theorem tailTrace_5220084 : CollatzResearch.WordTrace tailWord_5220084 prefixEnd_5220084 893470716281553210347759 := by
  unfold tailWord_5220084
  simp only [CollatzResearch.WordTrace]
  refine ⟨95196052410267331107413653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126928069880356441476551537 95196052410267331107413653)
  ·
    refine ⟨4462314956731281145660015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 95196052410267331107413653 4462314956731281145660015)
    ·
      refine ⟨6693472435096921718490023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4462314956731281145660015 6693472435096921718490023)
      ·
        refine ⟨10040208652645382577735035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6693472435096921718490023 10040208652645382577735035)
        ·
          refine ⟨15060312978968073866602553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10040208652645382577735035 15060312978968073866602553)
          ·
            refine ⟨11295234734226055399951915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15060312978968073866602553 11295234734226055399951915)
            ·
              refine ⟨16942852101339083099927873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11295234734226055399951915 16942852101339083099927873)
              ·
                refine ⟨12707139076004312324945905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16942852101339083099927873 12707139076004312324945905)
                ·
                  refine ⟨9530354307003234243709429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12707139076004312324945905 9530354307003234243709429)
                  ·
                    refine ⟨893470716281553210347759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9530354307003234243709429 893470716281553210347759)
                    ·
                      rfl

theorem cell23_5220084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_5220084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5220084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5220084 prefixEnd_5220084 := by exact prefixLift 5220084
  have htrace : WordTrace (prefixWord ++ tailWord_5220084) baseStart_5220084 baseEnd_5220084 := by
    simpa [prefixWord, tailWord_5220084, baseEnd_5220084] using wordTrace_append hprefix tailTrace_5220084
  have hstable : (prefixWord ++ tailWord_5220084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5220084).length < 2 ^ (prefixWord ++ tailWord_5220084).sum := by decide
  have hdescent : baseEnd_5220084 < baseStart_5220084 := by decide
  rcases family_descends (prefixWord ++ tailWord_5220084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5220097 : List Nat := [1, 2, 4, 1, 1, 1, 2, 6, 1, 4]
def baseStart_5220097 : Nat := 118140960795 + 5220097 * 2 ^ 59
def prefixEnd_5220097 : Nat := 4983230072969 + 3 ^ 40 * 5220097 * 2
def baseEnd_5220097 : Nat := 893472941364389360060239

theorem tailTrace_5220097 : CollatzResearch.WordTrace tailWord_5220097 prefixEnd_5220097 893472941364389360060239 := by
  unfold tailWord_5220097
  simp only [CollatzResearch.WordTrace]
  refine ⟨190392578969487565435050545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126928385979658376956700363 190392578969487565435050545)
  ·
    refine ⟨142794434227115674076287909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190392578969487565435050545 142794434227115674076287909)
    ·
      refine ⟨26773956417584188889303983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 142794434227115674076287909 26773956417584188889303983)
      ·
        refine ⟨40160934626376283333955975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26773956417584188889303983 40160934626376283333955975)
        ·
          refine ⟨60241401939564425000933963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40160934626376283333955975 60241401939564425000933963)
          ·
            refine ⟨90362102909346637501400945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60241401939564425000933963 90362102909346637501400945)
            ·
              refine ⟨67771577182009978126050709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90362102909346637501400945 67771577182009978126050709)
              ·
                refine ⟨3176792680406717724658627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 67771577182009978126050709 3176792680406717724658627)
                ·
                  refine ⟨4765189020610076586987941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3176792680406717724658627 4765189020610076586987941)
                  ·
                    refine ⟨893472941364389360060239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4765189020610076586987941 893472941364389360060239)
                    ·
                      rfl

theorem cell23_5220097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 6, 1, 4].length) (baseStart_5220097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5220097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5220097 prefixEnd_5220097 := by exact prefixLift 5220097
  have htrace : WordTrace (prefixWord ++ tailWord_5220097) baseStart_5220097 baseEnd_5220097 := by
    simpa [prefixWord, tailWord_5220097, baseEnd_5220097] using wordTrace_append hprefix tailTrace_5220097
  have hstable : (prefixWord ++ tailWord_5220097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5220097).length < 2 ^ (prefixWord ++ tailWord_5220097).sum := by decide
  have hdescent : baseEnd_5220097 < baseStart_5220097 := by decide
  rcases family_descends (prefixWord ++ tailWord_5220097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5220123 : List Nat := [1, 1, 1, 1, 1, 1, 4, 5, 3, 5]
def baseStart_5220123 : Nat := 118140960795 + 5220123 * 2 ^ 59
def prefixEnd_5220123 : Nat := 4983230072969 + 3 ^ 40 * 5220123 * 2
def baseEnd_5220123 : Nat := 893477391530061659485199

theorem tailTrace_5220123 : CollatzResearch.WordTrace tailWord_5220123 prefixEnd_5220123 893477391530061659485199 := by
  unfold tailWord_5220123
  simp only [CollatzResearch.WordTrace]
  refine ⟨190393527267393371875497023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126929018178262247916998015 190393527267393371875497023)
  ·
    refine ⟨285590290901090057813245535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190393527267393371875497023 285590290901090057813245535)
    ·
      refine ⟨428385436351635086719868303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285590290901090057813245535 428385436351635086719868303)
      ·
        refine ⟨642578154527452630079802455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 428385436351635086719868303 642578154527452630079802455)
        ·
          refine ⟨963867231791178945119703683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 642578154527452630079802455 963867231791178945119703683)
          ·
            refine ⟨1445800847686768417679555525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 963867231791178945119703683 1445800847686768417679555525)
            ·
              refine ⟨271087658941269078314916661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1445800847686768417679555525 271087658941269078314916661)
              ·
                refine ⟨25414468025743976092023437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 271087658941269078314916661 25414468025743976092023437)
                ·
                  refine ⟨9530425509653991034508789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25414468025743976092023437 9530425509653991034508789)
                  ·
                    refine ⟨893477391530061659485199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9530425509653991034508789 893477391530061659485199)
                    ·
                      rfl

theorem cell23_5220123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 3, 5].length) (baseStart_5220123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5220123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5220123 prefixEnd_5220123 := by exact prefixLift 5220123
  have htrace : WordTrace (prefixWord ++ tailWord_5220123) baseStart_5220123 baseEnd_5220123 := by
    simpa [prefixWord, tailWord_5220123, baseEnd_5220123] using wordTrace_append hprefix tailTrace_5220123
  have hstable : (prefixWord ++ tailWord_5220123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5220123).length < 2 ^ (prefixWord ++ tailWord_5220123).sum := by decide
  have hdescent : baseEnd_5220123 < baseStart_5220123 := by decide
  rcases family_descends (prefixWord ++ tailWord_5220123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5220148 : List Nat := [2, 5, 1, 1, 2, 3, 2, 2, 1, 4]
def baseStart_5220148 : Nat := 118140960795 + 5220148 * 2 ^ 59
def prefixEnd_5220148 : Nat := 4983230072969 + 3 ^ 40 * 5220148 * 2
def baseEnd_5220148 : Nat := 893481670535515793547661

theorem tailTrace_5220148 : CollatzResearch.WordTrace tailWord_5220148 prefixEnd_5220148 893481670535515793547661 := by
  unfold tailWord_5220148
  simp only [CollatzResearch.WordTrace]
  refine ⟨95197219546151400572578549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126929626061535200763438065 95197219546151400572578549)
  ·
    refine ⟨8924739332451693803679239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 95197219546151400572578549 8924739332451693803679239)
    ·
      refine ⟨13387108998677540705518859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8924739332451693803679239 13387108998677540705518859)
      ·
        refine ⟨20080663498016311058278289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13387108998677540705518859 20080663498016311058278289)
        ·
          refine ⟨15060497623512233293708717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20080663498016311058278289 15060497623512233293708717)
          ·
            refine ⟨5647686608817087485140769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15060497623512233293708717 5647686608817087485140769)
            ·
              refine ⟨4235764956612815613855577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5647686608817087485140769 4235764956612815613855577)
              ·
                refine ⟨3176823717459611710391683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4235764956612815613855577 3176823717459611710391683)
                ·
                  refine ⟨4765235576189417565587525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3176823717459611710391683 4765235576189417565587525)
                  ·
                    refine ⟨893481670535515793547661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4765235576189417565587525 893481670535515793547661)
                    ·
                      rfl

theorem cell23_5220148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_5220148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5220148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5220148 prefixEnd_5220148 := by exact prefixLift 5220148
  have htrace : WordTrace (prefixWord ++ tailWord_5220148) baseStart_5220148 baseEnd_5220148 := by
    simpa [prefixWord, tailWord_5220148, baseEnd_5220148] using wordTrace_append hprefix tailTrace_5220148
  have hstable : (prefixWord ++ tailWord_5220148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5220148).length < 2 ^ (prefixWord ++ tailWord_5220148).sum := by decide
  have hdescent : baseEnd_5220148 < baseStart_5220148 := by decide
  rcases family_descends (prefixWord ++ tailWord_5220148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5220160 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 4, 6, 2]
def baseStart_5220160 : Nat := 118140960795 + 5220160 * 2 ^ 59
def prefixEnd_5220160 : Nat := 4983230072969 + 3 ^ 40 * 5220160 * 2
def baseEnd_5220160 : Nat := 2680451173374401333692927

theorem tailTrace_5220160 : CollatzResearch.WordTrace tailWord_5220160 prefixEnd_5220160 2680451173374401333692927 := by
  unfold tailWord_5220160
  simp only [CollatzResearch.WordTrace]
  refine ⟨95197438384129663597296967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126929917845506218129729289 95197438384129663597296967)
  ·
    refine ⟨142796157576194495395945451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95197438384129663597296967 142796157576194495395945451)
    ·
      refine ⟨214194236364291743093918177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142796157576194495395945451 214194236364291743093918177)
      ·
        refine ⟨160645677273218807320438633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214194236364291743093918177 160645677273218807320438633)
        ·
          refine ⟨120484257954914105490328975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160645677273218807320438633 120484257954914105490328975)
          ·
            refine ⟨180726386932371158235493463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120484257954914105490328975 180726386932371158235493463)
            ·
              refine ⟨271089580398556737353240195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180726386932371158235493463 271089580398556737353240195)
              ·
                refine ⟨406634370597835106029860293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 271089580398556737353240195 406634370597835106029860293)
                ·
                  refine ⟨76243944487094082380598805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 406634370597835106029860293 76243944487094082380598805)
                  ·
                    refine ⟨3573934897832535111590569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 76243944487094082380598805 3573934897832535111590569)
                    ·
                      refine ⟨2680451173374401333692927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3573934897832535111590569 2680451173374401333692927)
                      ·
                        rfl

theorem cell23_5220160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 4, 6, 2].length) (baseStart_5220160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5220160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5220160 prefixEnd_5220160 := by exact prefixLift 5220160
  have htrace : WordTrace (prefixWord ++ tailWord_5220160) baseStart_5220160 baseEnd_5220160 := by
    simpa [prefixWord, tailWord_5220160, baseEnd_5220160] using wordTrace_append hprefix tailTrace_5220160
  have hstable : (prefixWord ++ tailWord_5220160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5220160).length < 2 ^ (prefixWord ++ tailWord_5220160).sum := by decide
  have hdescent : baseEnd_5220160 < baseStart_5220160 := by decide
  rcases family_descends (prefixWord ++ tailWord_5220160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5220170 : List Nat := [3, 1, 2, 1, 1, 1, 6, 1, 1, 6]
def baseStart_5220170 : Nat := 118140960795 + 5220170 * 2 ^ 59
def prefixEnd_5220170 : Nat := 4983230072969 + 3 ^ 40 * 5220170 * 2
def baseEnd_5220170 : Nat := 893485436060315431522627

theorem tailTrace_5220170 : CollatzResearch.WordTrace tailWord_5220170 prefixEnd_5220170 893485436060315431522627 := by
  unfold tailWord_5220170
  simp only [CollatzResearch.WordTrace]
  refine ⟨47598810374555774725614491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126930160998815399268305309 47598810374555774725614491)
  ·
    refine ⟨71398215561833662088421737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47598810374555774725614491 71398215561833662088421737)
    ·
      refine ⟨53548661671375246566316303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71398215561833662088421737 53548661671375246566316303)
      ·
        refine ⟨80322992507062869849474455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53548661671375246566316303 80322992507062869849474455)
        ·
          refine ⟨120484488760594304774211683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80322992507062869849474455 120484488760594304774211683)
          ·
            refine ⟨180726733140891457161317525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120484488760594304774211683 180726733140891457161317525)
            ·
              refine ⟨8471565615979287054436759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 180726733140891457161317525 8471565615979287054436759)
              ·
                refine ⟨12707348423968930581655139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8471565615979287054436759 12707348423968930581655139)
                ·
                  refine ⟨19061022635953395872482709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12707348423968930581655139 19061022635953395872482709)
                  ·
                    refine ⟨893485436060315431522627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19061022635953395872482709 893485436060315431522627)
                    ·
                      rfl

theorem cell23_5220170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 1, 1, 6].length) (baseStart_5220170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5220170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5220170 prefixEnd_5220170 := by exact prefixLift 5220170
  have htrace : WordTrace (prefixWord ++ tailWord_5220170) baseStart_5220170 baseEnd_5220170 := by
    simpa [prefixWord, tailWord_5220170, baseEnd_5220170] using wordTrace_append hprefix tailTrace_5220170
  have hstable : (prefixWord ++ tailWord_5220170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5220170).length < 2 ^ (prefixWord ++ tailWord_5220170).sum := by decide
  have hdescent : baseEnd_5220170 < baseStart_5220170 := by decide
  rcases family_descends (prefixWord ++ tailWord_5220170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5220188 : List Nat := [2, 2, 4, 2, 2, 1, 2, 3, 1, 1, 3]
def baseStart_5220188 : Nat := 118140960795 + 5220188 * 2 ^ 59
def prefixEnd_5220188 : Nat := 4983230072969 + 3 ^ 40 * 5220188 * 2
def baseEnd_5220188 : Nat := 2680465550832727224142799

theorem tailTrace_5220188 : CollatzResearch.WordTrace tailWord_5220188 prefixEnd_5220188 2680465550832727224142799 := by
  unfold tailWord_5220188
  simp only [CollatzResearch.WordTrace]
  refine ⟨95197949006078943988306609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126930598674771925317742145 95197949006078943988306609)
  ·
    refine ⟨71398461754559207991229957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95197949006078943988306609 71398461754559207991229957)
    ·
      refine ⟨13387211578979851498355617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71398461754559207991229957 13387211578979851498355617)
      ·
        refine ⟨10040408684234888623766713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13387211578979851498355617 10040408684234888623766713)
        ·
          refine ⟨7530306513176166467825035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10040408684234888623766713 7530306513176166467825035)
          ·
            refine ⟨11295459769764249701737553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7530306513176166467825035 11295459769764249701737553)
            ·
              refine ⟨8471594827323187276303165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11295459769764249701737553 8471594827323187276303165)
              ·
                refine ⟨3176848060246195228613687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8471594827323187276303165 3176848060246195228613687)
                ·
                  refine ⟨4765272090369292842920531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3176848060246195228613687 4765272090369292842920531)
                  ·
                    refine ⟨7147908135553939264380797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4765272090369292842920531 7147908135553939264380797)
                    ·
                      refine ⟨2680465550832727224142799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7147908135553939264380797 2680465550832727224142799)
                      ·
                        rfl

theorem cell23_5220188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_5220188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5220188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5220188 prefixEnd_5220188 := by exact prefixLift 5220188
  have htrace : WordTrace (prefixWord ++ tailWord_5220188) baseStart_5220188 baseEnd_5220188 := by
    simpa [prefixWord, tailWord_5220188, baseEnd_5220188] using wordTrace_append hprefix tailTrace_5220188
  have hstable : (prefixWord ++ tailWord_5220188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5220188).length < 2 ^ (prefixWord ++ tailWord_5220188).sum := by decide
  have hdescent : baseEnd_5220188 < baseStart_5220188 := by decide
  rcases family_descends (prefixWord ++ tailWord_5220188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5220194 : List Nat := [3, 3, 2, 1, 2, 2, 1, 3, 1, 1, 4]
def baseStart_5220194 : Nat := 118140960795 + 5220194 * 2 ^ 59
def prefixEnd_5220194 : Nat := 4983230072969 + 3 ^ 40 * 5220194 * 2
def baseEnd_5220194 : Nat := 2680468631716654200667771

theorem tailTrace_5220194 : CollatzResearch.WordTrace tailWord_5220194 prefixEnd_5220194 2680468631716654200667771 := by
  unfold tailWord_5220194
  simp only [CollatzResearch.WordTrace]
  refine ⟨47599029212534037750332909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126930744566757434000887757 47599029212534037750332909)
  ·
    refine ⟨17849635954700264156374841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47599029212534037750332909 17849635954700264156374841)
    ·
      refine ⟨13387226966025198117281131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17849635954700264156374841 13387226966025198117281131)
      ·
        refine ⟨20080840449037797175921697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13387226966025198117281131 20080840449037797175921697)
        ·
          refine ⟨15060630336778347881941273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20080840449037797175921697 15060630336778347881941273)
          ·
            refine ⟨11295472752583760911455955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15060630336778347881941273 11295472752583760911455955)
            ·
              refine ⟨16943209128875641367183933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11295472752583760911455955 16943209128875641367183933)
              ·
                refine ⟨6353703423328365512693975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16943209128875641367183933 6353703423328365512693975)
                ·
                  refine ⟨9530555134992548269040963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6353703423328365512693975 9530555134992548269040963)
                  ·
                    refine ⟨14295832702488822403561445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9530555134992548269040963 14295832702488822403561445)
                    ·
                      refine ⟨2680468631716654200667771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14295832702488822403561445 2680468631716654200667771)
                      ·
                        rfl

theorem cell23_5220194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_5220194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5220194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5220194 prefixEnd_5220194 := by exact prefixLift 5220194
  have htrace : WordTrace (prefixWord ++ tailWord_5220194) baseStart_5220194 baseEnd_5220194 := by
    simpa [prefixWord, tailWord_5220194, baseEnd_5220194] using wordTrace_append hprefix tailTrace_5220194
  have hstable : (prefixWord ++ tailWord_5220194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5220194).length < 2 ^ (prefixWord ++ tailWord_5220194).sum := by decide
  have hdescent : baseEnd_5220194 < baseStart_5220194 := by decide
  rcases family_descends (prefixWord ++ tailWord_5220194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5220203 : List Nat := [1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 6]
def baseStart_5220203 : Nat := 118140960795 + 5220203 * 2 ^ 59
def prefixEnd_5220203 : Nat := 4983230072969 + 3 ^ 40 * 5220203 * 2
def baseEnd_5220203 : Nat := 2680473253042544665455229

theorem tailTrace_5220203 : CollatzResearch.WordTrace tailWord_5220203 prefixEnd_5220203 2680473253042544665455229 := by
  unfold tailWord_5220203
  simp only [CollatzResearch.WordTrace]
  refine ⟨190396445107103545538409263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126930963404735697025606175 190396445107103545538409263)
  ·
    refine ⟨285594667660655318307613895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190396445107103545538409263 285594667660655318307613895)
    ·
      refine ⟨428392001490982977461420843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285594667660655318307613895 428392001490982977461420843)
      ·
        refine ⟨642588002236474466192131265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 428392001490982977461420843 642588002236474466192131265)
        ·
          refine ⟨481941001677355849644098449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 642588002236474466192131265 481941001677355849644098449)
          ·
            refine ⟨361455751258016887233073837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 481941001677355849644098449 361455751258016887233073837)
            ·
              refine ⟨135545906721756332712402689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 361455751258016887233073837 135545906721756332712402689)
              ·
                refine ⟨101659430041317249534302017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 135545906721756332712402689 101659430041317249534302017)
                ·
                  refine ⟨76244572530987937150726513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101659430041317249534302017 76244572530987937150726513)
                  ·
                    refine ⟨57183429398240952863044885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 76244572530987937150726513 57183429398240952863044885)
                    ·
                      refine ⟨2680473253042544665455229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57183429398240952863044885 2680473253042544665455229)
                      ·
                        rfl

theorem cell23_5220203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 6].length) (baseStart_5220203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5220203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5220203 prefixEnd_5220203 := by exact prefixLift 5220203
  have htrace : WordTrace (prefixWord ++ tailWord_5220203) baseStart_5220203 baseEnd_5220203 := by
    simpa [prefixWord, tailWord_5220203, baseEnd_5220203] using wordTrace_append hprefix tailTrace_5220203
  have hstable : (prefixWord ++ tailWord_5220203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5220203).length < 2 ^ (prefixWord ++ tailWord_5220203).sum := by decide
  have hdescent : baseEnd_5220203 < baseStart_5220203 := by decide
  rcases family_descends (prefixWord ++ tailWord_5220203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5220204 : List Nat := [2, 2, 1, 1, 4, 4, 1, 2, 2, 4]
def baseStart_5220204 : Nat := 118140960795 + 5220204 * 2 ^ 59
def prefixEnd_5220204 : Nat := 4983230072969 + 3 ^ 40 * 5220204 * 2
def baseEnd_5220204 : Nat := 893491255507733053847575

theorem tailTrace_5220204 : CollatzResearch.WordTrace tailWord_5220204 prefixEnd_5220204 893491255507733053847575 := by
  unfold tailWord_5220204
  simp only [CollatzResearch.WordTrace]
  refine ⟨95198240790049961354597833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126930987720066615139463777 95198240790049961354597833)
  ·
    refine ⟨71398680592537471015948375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95198240790049961354597833 71398680592537471015948375)
    ·
      refine ⟨107098020888806206523922563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71398680592537471015948375 107098020888806206523922563)
      ·
        refine ⟨160647031333209309785883845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107098020888806206523922563 160647031333209309785883845)
        ·
          refine ⟨30121318374976745584853221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 160647031333209309785883845 30121318374976745584853221)
          ·
            refine ⟨5647747195308139797159979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30121318374976745584853221 5647747195308139797159979)
            ·
              refine ⟨8471620792962209695739969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5647747195308139797159979 8471620792962209695739969)
              ·
                refine ⟨6353715594721657271804977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8471620792962209695739969 6353715594721657271804977)
                ·
                  refine ⟨4765286696041242953853733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6353715594721657271804977 4765286696041242953853733)
                  ·
                    refine ⟨893491255507733053847575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4765286696041242953853733 893491255507733053847575)
                    ·
                      rfl

theorem cell23_5220204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 4].length) (baseStart_5220204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5220204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5220204 prefixEnd_5220204 := by exact prefixLift 5220204
  have htrace : WordTrace (prefixWord ++ tailWord_5220204) baseStart_5220204 baseEnd_5220204 := by
    simpa [prefixWord, tailWord_5220204, baseEnd_5220204] using wordTrace_append hprefix tailTrace_5220204
  have hstable : (prefixWord ++ tailWord_5220204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5220204).length < 2 ^ (prefixWord ++ tailWord_5220204).sum := by decide
  have hdescent : baseEnd_5220204 < baseStart_5220204 := by decide
  rcases family_descends (prefixWord ++ tailWord_5220204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5220214 : List Nat := [5, 1, 1, 3, 2, 1, 1, 2, 1, 1, 5]
def baseStart_5220214 : Nat := 118140960795 + 5220214 * 2 ^ 59
def prefixEnd_5220214 : Nat := 4983230072969 + 3 ^ 40 * 5220214 * 2
def baseEnd_5220214 : Nat := 2680478901329744122417679

theorem tailTrace_5220214 : CollatzResearch.WordTrace tailWord_5220214 prefixEnd_5220214 2680478901329744122417679 := by
  unfold tailWord_5220214
  simp only [CollatzResearch.WordTrace]
  refine ⟨11899802894378980901066231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 126931230873375796278039797 11899802894378980901066231)
  ·
    refine ⟨17849704341568471351599347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11899802894378980901066231 17849704341568471351599347)
    ·
      refine ⟨26774556512352707027399021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17849704341568471351599347 26774556512352707027399021)
      ·
        refine ⟨10040458692132265135274633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26774556512352707027399021 10040458692132265135274633)
        ·
          refine ⟨7530344019099198851455975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10040458692132265135274633 7530344019099198851455975)
          ·
            refine ⟨11295516028648798277183963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7530344019099198851455975 11295516028648798277183963)
            ·
              refine ⟨16943274042973197415775945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11295516028648798277183963 16943274042973197415775945)
              ·
                refine ⟨12707455532229898061831959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16943274042973197415775945 12707455532229898061831959)
                ·
                  refine ⟨19061183298344847092747939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12707455532229898061831959 19061183298344847092747939)
                  ·
                    refine ⟨28591774947517270639121909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19061183298344847092747939 28591774947517270639121909)
                    ·
                      refine ⟨2680478901329744122417679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28591774947517270639121909 2680478901329744122417679)
                      ·
                        rfl

theorem cell23_5220214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_5220214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5220214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5220214 prefixEnd_5220214 := by exact prefixLift 5220214
  have htrace : WordTrace (prefixWord ++ tailWord_5220214) baseStart_5220214 baseEnd_5220214 := by
    simpa [prefixWord, tailWord_5220214, baseEnd_5220214] using wordTrace_append hprefix tailTrace_5220214
  have hstable : (prefixWord ++ tailWord_5220214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5220214).length < 2 ^ (prefixWord ++ tailWord_5220214).sum := by decide
  have hdescent : baseEnd_5220214 < baseStart_5220214 := by decide
  rcases family_descends (prefixWord ++ tailWord_5220214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5220227 : List Nat := [1, 1, 1, 3, 4, 2, 3, 1, 1, 3, 3]
def baseStart_5220227 : Nat := 118140960795 + 5220227 * 2 ^ 59
def prefixEnd_5220227 : Nat := 4983230072969 + 3 ^ 40 * 5220227 * 2
def baseEnd_5220227 : Nat := 2680485576578252571555119

theorem tailTrace_5220227 : CollatzResearch.WordTrace tailWord_5220227 prefixEnd_5220227 2680485576578252571555119 := by
  unfold tailWord_5220227
  simp only [CollatzResearch.WordTrace]
  refine ⟨190397320459016597637282935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126931546972677731758188623 190397320459016597637282935)
  ·
    refine ⟨285595980688524896455924403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190397320459016597637282935 285595980688524896455924403)
    ·
      refine ⟨428393971032787344683886605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285595980688524896455924403 428393971032787344683886605)
      ·
        refine ⟨160647739137295254256457477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 428393971032787344683886605 160647739137295254256457477)
        ·
          refine ⟨30121451088242860173085777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 160647739137295254256457477 30121451088242860173085777)
          ·
            refine ⟨22591088316182145129814333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30121451088242860173085777 22591088316182145129814333)
            ·
              refine ⟨8471658118568304423680375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22591088316182145129814333 8471658118568304423680375)
              ·
                refine ⟨12707487177852456635520563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8471658118568304423680375 12707487177852456635520563)
                ·
                  refine ⟨19061230766778684953280845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12707487177852456635520563 19061230766778684953280845)
                  ·
                    refine ⟨7147961537542006857480317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19061230766778684953280845 7147961537542006857480317)
                    ·
                      refine ⟨2680485576578252571555119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7147961537542006857480317 2680485576578252571555119)
                      ·
                        rfl

theorem cell23_5220227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 1, 1, 3, 3].length) (baseStart_5220227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5220227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5220227 prefixEnd_5220227 := by exact prefixLift 5220227
  have htrace : WordTrace (prefixWord ++ tailWord_5220227) baseStart_5220227 baseEnd_5220227 := by
    simpa [prefixWord, tailWord_5220227, baseEnd_5220227] using wordTrace_append hprefix tailTrace_5220227
  have hstable : (prefixWord ++ tailWord_5220227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5220227).length < 2 ^ (prefixWord ++ tailWord_5220227).sum := by decide
  have hdescent : baseEnd_5220227 < baseStart_5220227 := by decide
  rcases family_descends (prefixWord ++ tailWord_5220227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5220234 : List Nat := [3, 1, 2, 4, 2, 2, 2, 7]
def baseStart_5220234 : Nat := 118140960795 + 5220234 * 2 ^ 59
def prefixEnd_5220234 : Nat := 4983230072969 + 3 ^ 40 * 5220234 * 2
def baseEnd_5220234 : Nat := 99277376701586446080281

theorem tailTrace_5220234 : CollatzResearch.WordTrace tailWord_5220234 prefixEnd_5220234 99277376701586446080281 := by
  unfold tailWord_5220234
  simp only [CollatzResearch.WordTrace]
  refine ⟨47599393942497809458196939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126931717179994158555191837 47599393942497809458196939)
  ·
    refine ⟨71399090913746714187295409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47599393942497809458196939 71399090913746714187295409)
    ·
      refine ⟨53549318185310035640471557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71399090913746714187295409 53549318185310035640471557)
      ·
        refine ⟨10040497159745631682588417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53549318185310035640471557 10040497159745631682588417)
        ·
          refine ⟨7530372869809223761941313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10040497159745631682588417 7530372869809223761941313)
          ·
            refine ⟨5647779652356917821455985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7530372869809223761941313 5647779652356917821455985)
            ·
              refine ⟨4235834739267688366091989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5647779652356917821455985 4235834739267688366091989)
              ·
                refine ⟨99277376701586446080281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4235834739267688366091989 99277376701586446080281)
                ·
                  rfl

theorem cell23_5220234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 2, 7].length) (baseStart_5220234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5220234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5220234 prefixEnd_5220234 := by exact prefixLift 5220234
  have htrace : WordTrace (prefixWord ++ tailWord_5220234) baseStart_5220234 baseEnd_5220234 := by
    simpa [prefixWord, tailWord_5220234, baseEnd_5220234] using wordTrace_append hprefix tailTrace_5220234
  have hstable : (prefixWord ++ tailWord_5220234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5220234).length < 2 ^ (prefixWord ++ tailWord_5220234).sum := by decide
  have hdescent : baseEnd_5220234 < baseStart_5220234 := by decide
  rcases family_descends (prefixWord ++ tailWord_5220234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5220244 : List Nat := [2, 4, 2, 1, 1, 2, 1, 2, 4, 1, 3]
def baseStart_5220244 : Nat := 118140960795 + 5220244 * 2 ^ 59
def prefixEnd_5220244 : Nat := 4983230072969 + 3 ^ 40 * 5220244 * 2
def baseEnd_5220244 : Nat := 2680494305749379005042541

theorem tailTrace_5220244 : CollatzResearch.WordTrace tailWord_5220244 prefixEnd_5220244 2680494305749379005042541 := by
  unfold tailWord_5220244
  simp only [CollatzResearch.WordTrace]
  refine ⟨95198970249977504770325893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126931960333303339693767857 95198970249977504770325893)
  ·
    refine ⟨17849806921870782144436105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95198970249977504770325893 17849806921870782144436105)
    ·
      refine ⟨13387355191403086608327079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17849806921870782144436105 13387355191403086608327079)
      ·
        refine ⟨20081032787104629912490619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13387355191403086608327079 20081032787104629912490619)
        ·
          refine ⟨30121549180656944868735929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20081032787104629912490619 30121549180656944868735929)
          ·
            refine ⟨22591161885492708651551947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30121549180656944868735929 22591161885492708651551947)
            ·
              refine ⟨33886742828239062977327921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22591161885492708651551947 33886742828239062977327921)
              ·
                refine ⟨25415057121179297232995941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33886742828239062977327921 25415057121179297232995941)
                ·
                  refine ⟨4765323210221118231186739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25415057121179297232995941 4765323210221118231186739)
                  ·
                    refine ⟨7147984815331677346780109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4765323210221118231186739 7147984815331677346780109)
                    ·
                      refine ⟨2680494305749379005042541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7147984815331677346780109 2680494305749379005042541)
                      ·
                        rfl

theorem cell23_5220244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_5220244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5220244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5220244 prefixEnd_5220244 := by exact prefixLift 5220244
  have htrace : WordTrace (prefixWord ++ tailWord_5220244) baseStart_5220244 baseEnd_5220244 := by
    simpa [prefixWord, tailWord_5220244, baseEnd_5220244] using wordTrace_append hprefix tailTrace_5220244
  have hstable : (prefixWord ++ tailWord_5220244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5220244).length < 2 ^ (prefixWord ++ tailWord_5220244).sum := by decide
  have hdescent : baseEnd_5220244 < baseStart_5220244 := by decide
  rcases family_descends (prefixWord ++ tailWord_5220244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5220280 : List Nat := [2, 1, 2, 1, 2, 3, 2, 1, 1, 4, 4]
def baseStart_5220280 : Nat := 118140960795 + 5220280 * 2 ^ 59
def prefixEnd_5220280 : Nat := 4983230072969 + 3 ^ 40 * 5220280 * 2
def baseEnd_5220280 : Nat := 2680512791052940864192375

theorem tailTrace_5220280 : CollatzResearch.WordTrace tailWord_5220280 prefixEnd_5220280 2680512791052940864192375 := by
  unfold tailWord_5220280
  simp only [CollatzResearch.WordTrace]
  refine ⟨95199626763912293844481147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126932835685216391792641529 95199626763912293844481147)
  ·
    refine ⟨142799440145868440766721721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95199626763912293844481147 142799440145868440766721721)
    ·
      refine ⟨107099580109401330575041291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142799440145868440766721721 107099580109401330575041291)
      ·
        refine ⟨160649370164101995862561937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107099580109401330575041291 160649370164101995862561937)
        ·
          refine ⟨120487027623076496896921453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160649370164101995862561937 120487027623076496896921453)
          ·
            refine ⟨45182635358653686336345545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120487027623076496896921453 45182635358653686336345545)
            ·
              refine ⟨33886976518990264752259159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45182635358653686336345545 33886976518990264752259159)
              ·
                refine ⟨50830464778485397128388739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33886976518990264752259159 50830464778485397128388739)
                ·
                  refine ⟨76245697167728095692583109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50830464778485397128388739 76245697167728095692583109)
                  ·
                    refine ⟨14296068218949017942359333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 76245697167728095692583109 14296068218949017942359333)
                    ·
                      refine ⟨2680512791052940864192375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14296068218949017942359333 2680512791052940864192375)
                      ·
                        rfl

theorem cell23_5220280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 1, 4, 4].length) (baseStart_5220280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5220280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5220280 prefixEnd_5220280 := by exact prefixLift 5220280
  have htrace : WordTrace (prefixWord ++ tailWord_5220280) baseStart_5220280 baseEnd_5220280 := by
    simpa [prefixWord, tailWord_5220280, baseEnd_5220280] using wordTrace_append hprefix tailTrace_5220280
  have hstable : (prefixWord ++ tailWord_5220280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5220280).length < 2 ^ (prefixWord ++ tailWord_5220280).sum := by decide
  have hdescent : baseEnd_5220280 < baseStart_5220280 := by decide
  rcases family_descends (prefixWord ++ tailWord_5220280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5220334 : List Nat := [4, 1, 2, 1, 3, 2, 1, 1, 2, 3, 3]
def baseStart_5220334 : Nat := 118140960795 + 5220334 * 2 ^ 59
def prefixEnd_5220334 : Nat := 4983230072969 + 3 ^ 40 * 5220334 * 2
def baseEnd_5220334 : Nat := 2680540519008283652917127

theorem tailTrace_5220334 : CollatzResearch.WordTrace tailWord_5220334 prefixEnd_5220334 2680540519008283652917127 := by
  unfold tailWord_5220334
  simp only [CollatzResearch.WordTrace]
  refine ⟨23800152883703619363928507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126934148713085969940952037 23800152883703619363928507)
  ·
    refine ⟨35700229325555429045892761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23800152883703619363928507 35700229325555429045892761)
    ·
      refine ⟨26775171994166571784419571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35700229325555429045892761 26775171994166571784419571)
      ·
        refine ⟨40162757991249857676629357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26775171994166571784419571 40162757991249857676629357)
        ·
          refine ⟨15061034246718696628736009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40162757991249857676629357 15061034246718696628736009)
          ·
            refine ⟨11295775685039022471552007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15061034246718696628736009 11295775685039022471552007)
            ·
              refine ⟨16943663527558533707328011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11295775685039022471552007 16943663527558533707328011)
              ·
                refine ⟨25415495291337800560992017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16943663527558533707328011 25415495291337800560992017)
                ·
                  refine ⟨19061621468503350420744013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25415495291337800560992017 19061621468503350420744013)
                  ·
                    refine ⟨7148108050688756407779005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19061621468503350420744013 7148108050688756407779005)
                    ·
                      refine ⟨2680540519008283652917127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7148108050688756407779005 2680540519008283652917127)
                      ·
                        rfl

theorem cell23_5220334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 2, 3, 3].length) (baseStart_5220334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5220334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5220334 prefixEnd_5220334 := by exact prefixLift 5220334
  have htrace : WordTrace (prefixWord ++ tailWord_5220334) baseStart_5220334 baseEnd_5220334 := by
    simpa [prefixWord, tailWord_5220334, baseEnd_5220334] using wordTrace_append hprefix tailTrace_5220334
  have hstable : (prefixWord ++ tailWord_5220334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5220334).length < 2 ^ (prefixWord ++ tailWord_5220334).sum := by decide
  have hdescent : baseEnd_5220334 < baseStart_5220334 := by decide
  rcases family_descends (prefixWord ++ tailWord_5220334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5220357 : List Nat := [1, 3, 1, 1, 2, 5, 1, 1, 1, 3, 4]
def baseStart_5220357 : Nat := 118140960795 + 5220357 * 2 ^ 59
def prefixEnd_5220357 : Nat := 4983230072969 + 3 ^ 40 * 5220357 * 2
def baseEnd_5220357 : Nat := 2680552329063337062929521

theorem tailTrace_5220357 : CollatzResearch.WordTrace tailWord_5220357 prefixEnd_5220357 2680552329063337062929521 := by
  unfold tailWord_5220357
  simp only [CollatzResearch.WordTrace]
  refine ⟨190402061948545629839515325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126934707965697086559676883 190402061948545629839515325)
  ·
    refine ⟨71400773230704611189818247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190402061948545629839515325 71400773230704611189818247)
    ·
      refine ⟨107101159846056916784727371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71400773230704611189818247 107101159846056916784727371)
      ·
        refine ⟨160651739769085375177091057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107101159846056916784727371 160651739769085375177091057)
        ·
          refine ⟨120488804826814031382818293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160651739769085375177091057 120488804826814031382818293)
          ·
            refine ⟨11295825452513815442139215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 120488804826814031382818293 11295825452513815442139215)
            ·
              refine ⟨16943738178770723163208823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11295825452513815442139215 16943738178770723163208823)
              ·
                refine ⟨25415607268156084744813235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16943738178770723163208823 25415607268156084744813235)
                ·
                  refine ⟨38123410902234127117219853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25415607268156084744813235 38123410902234127117219853)
                  ·
                    refine ⟨14296279088337797668957445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38123410902234127117219853 14296279088337797668957445)
                    ·
                      refine ⟨2680552329063337062929521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14296279088337797668957445 2680552329063337062929521)
                      ·
                        rfl

theorem cell23_5220357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 3, 4].length) (baseStart_5220357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5220357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5220357 prefixEnd_5220357 := by exact prefixLift 5220357
  have htrace : WordTrace (prefixWord ++ tailWord_5220357) baseStart_5220357 baseEnd_5220357 := by
    simpa [prefixWord, tailWord_5220357, baseEnd_5220357] using wordTrace_append hprefix tailTrace_5220357
  have hstable : (prefixWord ++ tailWord_5220357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5220357).length < 2 ^ (prefixWord ++ tailWord_5220357).sum := by decide
  have hdescent : baseEnd_5220357 < baseStart_5220357 := by decide
  rcases family_descends (prefixWord ++ tailWord_5220357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5220377 : List Nat := [1, 2, 1, 2, 1, 1, 3, 3, 4, 2, 3]
def baseStart_5220377 : Nat := 118140960795 + 5220377 * 2 ^ 59
def prefixEnd_5220377 : Nat := 4983230072969 + 3 ^ 40 * 5220377 * 2
def baseEnd_5220377 : Nat := 2680562598676426984679429

theorem tailTrace_5220377 : CollatzResearch.WordTrace tailWord_5220377 prefixEnd_5220377 2680562598676426984679429 := by
  unfold tailWord_5220377
  simp only [CollatzResearch.WordTrace]
  refine ⟨190402791408473173255243385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126935194272315448836828923 190402791408473173255243385)
  ·
    refine ⟨142802093556354879941432539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190402791408473173255243385 142802093556354879941432539)
    ·
      refine ⟨214203140334532319912148809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142802093556354879941432539 214203140334532319912148809)
      ·
        refine ⟨160652355250899239934111607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214203140334532319912148809 160652355250899239934111607)
        ·
          refine ⟨240978532876348859901167411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160652355250899239934111607 240978532876348859901167411)
          ·
            refine ⟨361467799314523289851751117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240978532876348859901167411 361467799314523289851751117)
            ·
              refine ⟨135550424742946233694406669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 361467799314523289851751117 135550424742946233694406669)
              ·
                refine ⟨50831409278604837635402501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 135550424742946233694406669 50831409278604837635402501)
                ·
                  refine ⟨9530889239738407056637969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50831409278604837635402501 9530889239738407056637969)
                  ·
                    refine ⟨7148166929803805292478477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9530889239738407056637969 7148166929803805292478477)
                    ·
                      refine ⟨2680562598676426984679429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7148166929803805292478477 2680562598676426984679429)
                      ·
                        rfl

theorem cell23_5220377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 4, 2, 3].length) (baseStart_5220377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5220377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5220377 prefixEnd_5220377 := by exact prefixLift 5220377
  have htrace : WordTrace (prefixWord ++ tailWord_5220377) baseStart_5220377 baseEnd_5220377 := by
    simpa [prefixWord, tailWord_5220377, baseEnd_5220377] using wordTrace_append hprefix tailTrace_5220377
  have hstable : (prefixWord ++ tailWord_5220377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5220377).length < 2 ^ (prefixWord ++ tailWord_5220377).sum := by decide
  have hdescent : baseEnd_5220377 < baseStart_5220377 := by decide
  rcases family_descends (prefixWord ++ tailWord_5220377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5220394 : List Nat := [3, 1, 4, 1, 2, 1, 1, 2, 1, 4, 3]
def baseStart_5220394 : Nat := 118140960795 + 5220394 * 2 ^ 59
def prefixEnd_5220394 : Nat := 4983230072969 + 3 ^ 40 * 5220394 * 2
def baseEnd_5220394 : Nat := 2680571327847553418166851

theorem tailTrace_5220394 : CollatzResearch.WordTrace tailWord_5220394 prefixEnd_5220394 2680571327847553418166851 := by
  unfold tailWord_5220394
  simp only [CollatzResearch.WordTrace]
  refine ⟨47600852862352896289653059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126935607632941056772408157 47600852862352896289653059)
  ·
    refine ⟨71401279293529344434479589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47600852862352896289653059 71401279293529344434479589)
    ·
      refine ⟨13387739867536752081464923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71401279293529344434479589 13387739867536752081464923)
      ·
        refine ⟨20081609801305128122197385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13387739867536752081464923 20081609801305128122197385)
        ·
          refine ⟨15061207350978846091648039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20081609801305128122197385 15061207350978846091648039)
          ·
            refine ⟨22591811026468269137472059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15061207350978846091648039 22591811026468269137472059)
            ·
              refine ⟨33887716539702403706208089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22591811026468269137472059 33887716539702403706208089)
              ·
                refine ⟨25415787404776802779656067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33887716539702403706208089 25415787404776802779656067)
                ·
                  refine ⟨38123681107165204169484101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25415787404776802779656067 38123681107165204169484101)
                  ·
                    refine ⟨7148190207593475781778269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38123681107165204169484101 7148190207593475781778269)
                    ·
                      refine ⟨2680571327847553418166851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7148190207593475781778269 2680571327847553418166851)
                      ·
                        rfl

theorem cell23_5220394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_5220394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5220394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5220394 prefixEnd_5220394 := by exact prefixLift 5220394
  have htrace : WordTrace (prefixWord ++ tailWord_5220394) baseStart_5220394 baseEnd_5220394 := by
    simpa [prefixWord, tailWord_5220394, baseEnd_5220394] using wordTrace_append hprefix tailTrace_5220394
  have hstable : (prefixWord ++ tailWord_5220394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5220394).length < 2 ^ (prefixWord ++ tailWord_5220394).sum := by decide
  have hdescent : baseEnd_5220394 < baseStart_5220394 := by decide
  rcases family_descends (prefixWord ++ tailWord_5220394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5220457 : List Nat := [1, 2, 1, 1, 1, 5, 2, 3, 1, 6]
def baseStart_5220457 : Nat := 118140960795 + 5220457 * 2 ^ 59
def prefixEnd_5220457 : Nat := 4983230072969 + 3 ^ 40 * 5220457 * 2
def baseEnd_5220457 : Nat := 893534559042928890559687

theorem tailTrace_5220457 : CollatzResearch.WordTrace tailWord_5220457 prefixEnd_5220457 893534559042928890559687 := by
  unfold tailWord_5220457
  simp only [CollatzResearch.WordTrace]
  refine ⟨190405709248183346918155625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126937139498788897945437083 190405709248183346918155625)
  ·
    refine ⟨142804281936137510188616719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190405709248183346918155625 142804281936137510188616719)
    ·
      refine ⟨214206422904206265282925079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142804281936137510188616719 214206422904206265282925079)
      ·
        refine ⟨321309634356309397924387619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214206422904206265282925079 321309634356309397924387619)
        ·
          refine ⟨481964451534464096886581429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 321309634356309397924387619 481964451534464096886581429)
          ·
            refine ⟨45184167331356009083117009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 481964451534464096886581429 45184167331356009083117009)
            ·
              refine ⟨33888125498517006812337757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45184167331356009083117009 33888125498517006812337757)
              ·
                refine ⟨12708047061943877554626659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33888125498517006812337757 12708047061943877554626659)
                ·
                  refine ⟨19062070592915816331939989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12708047061943877554626659 19062070592915816331939989)
                  ·
                    refine ⟨893534559042928890559687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19062070592915816331939989 893534559042928890559687)
                    ·
                      rfl

theorem cell23_5220457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 3, 1, 6].length) (baseStart_5220457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5220457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5220457 prefixEnd_5220457 := by exact prefixLift 5220457
  have htrace : WordTrace (prefixWord ++ tailWord_5220457) baseStart_5220457 baseEnd_5220457 := by
    simpa [prefixWord, tailWord_5220457, baseEnd_5220457] using wordTrace_append hprefix tailTrace_5220457
  have hstable : (prefixWord ++ tailWord_5220457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5220457).length < 2 ^ (prefixWord ++ tailWord_5220457).sum := by decide
  have hdescent : baseEnd_5220457 < baseStart_5220457 := by decide
  rcases family_descends (prefixWord ++ tailWord_5220457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5220464 : List Nat := [2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 4]
def baseStart_5220464 : Nat := 118140960795 + 5220464 * 2 ^ 59
def prefixEnd_5220464 : Nat := 4983230072969 + 3 ^ 40 * 5220464 * 2
def baseEnd_5220464 : Nat := 2680607271493368144291529

theorem tailTrace_5220464 : CollatzResearch.WordTrace tailWord_5220464 prefixEnd_5220464 2680607271493368144291529 := by
  unfold tailWord_5220464
  simp only [CollatzResearch.WordTrace]
  refine ⟨95202982279578993556830223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126937309706105324742440297 95202982279578993556830223)
  ·
    refine ⟨142804473419368490335245335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95202982279578993556830223 142804473419368490335245335)
    ·
      refine ⟨214206710129052735502868003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142804473419368490335245335 214206710129052735502868003)
      ·
        refine ⟨321310065193579103254302005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214206710129052735502868003 321310065193579103254302005)
        ·
          refine ⟨30122818611898040930090813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 321310065193579103254302005 30122818611898040930090813)
          ·
            refine ⟨11296056979461765348784055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30122818611898040930090813 11296056979461765348784055)
            ·
              refine ⟨16944085469192648023176083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11296056979461765348784055 16944085469192648023176083)
              ·
                refine ⟨25416128203788972034764125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16944085469192648023176083 25416128203788972034764125)
                ·
                  refine ⟨9531048076420864513036547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25416128203788972034764125 9531048076420864513036547)
                  ·
                    refine ⟨14296572114631296769554821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9531048076420864513036547 14296572114631296769554821)
                    ·
                      refine ⟨2680607271493368144291529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14296572114631296769554821 2680607271493368144291529)
                      ·
                        rfl

theorem cell23_5220464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 4].length) (baseStart_5220464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5220464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5220464 prefixEnd_5220464 := by exact prefixLift 5220464
  have htrace : WordTrace (prefixWord ++ tailWord_5220464) baseStart_5220464 baseEnd_5220464 := by
    simpa [prefixWord, tailWord_5220464, baseEnd_5220464] using wordTrace_append hprefix tailTrace_5220464
  have hstable : (prefixWord ++ tailWord_5220464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5220464).length < 2 ^ (prefixWord ++ tailWord_5220464).sum := by decide
  have hdescent : baseEnd_5220464 < baseStart_5220464 := by decide
  rcases family_descends (prefixWord ++ tailWord_5220464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5220498 : List Nat := [3, 2, 3, 1, 1, 1, 2, 3, 3, 2, 2]
def baseStart_5220498 : Nat := 118140960795 + 5220498 * 2 ^ 59
def prefixEnd_5220498 : Nat := 4983230072969 + 3 ^ 40 * 5220498 * 2
def baseEnd_5220498 : Nat := 2680624729835621011266373

theorem tailTrace_5220498 : CollatzResearch.WordTrace tailWord_5220498 prefixEnd_5220498 2680624729835621011266373 := by
  unfold tailWord_5220498
  simp only [CollatzResearch.WordTrace]
  refine ⟨47601801160258702730099537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126938136427356540613598765 47601801160258702730099537)
  ·
    refine ⟨35701350870194027047574653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47601801160258702730099537 35701350870194027047574653)
    ·
      refine ⟨13388006576322760142840495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35701350870194027047574653 13388006576322760142840495)
      ·
        refine ⟨20082009864484140214260743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13388006576322760142840495 20082009864484140214260743)
        ·
          refine ⟨30123014796726210321391115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20082009864484140214260743 30123014796726210321391115)
          ·
            refine ⟨45184522195089315482086673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30123014796726210321391115 45184522195089315482086673)
            ·
              refine ⟨33888391646316986611565005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45184522195089315482086673 33888391646316986611565005)
              ·
                refine ⟨12708146867368869979336877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33888391646316986611565005 12708146867368869979336877)
                ·
                  refine ⟨4765555075263326242251329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12708146867368869979336877 4765555075263326242251329)
                  ·
                    refine ⟨3574166306447494681688497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4765555075263326242251329 3574166306447494681688497)
                    ·
                      refine ⟨2680624729835621011266373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3574166306447494681688497 2680624729835621011266373)
                      ·
                        rfl

theorem cell23_5220498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 3, 3, 2, 2].length) (baseStart_5220498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5220498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5220498 prefixEnd_5220498 := by exact prefixLift 5220498
  have htrace : WordTrace (prefixWord ++ tailWord_5220498) baseStart_5220498 baseEnd_5220498 := by
    simpa [prefixWord, tailWord_5220498, baseEnd_5220498] using wordTrace_append hprefix tailTrace_5220498
  have hstable : (prefixWord ++ tailWord_5220498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5220498).length < 2 ^ (prefixWord ++ tailWord_5220498).sum := by decide
  have hdescent : baseEnd_5220498 < baseStart_5220498 := by decide
  rcases family_descends (prefixWord ++ tailWord_5220498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5220511 : List Nat := [1, 1, 2, 6, 1, 2, 2, 1, 1, 2, 4]
def baseStart_5220511 : Nat := 118140960795 + 5220511 * 2 ^ 59
def prefixEnd_5220511 : Nat := 4983230072969 + 3 ^ 40 * 5220511 * 2
def baseEnd_5220511 : Nat := 2680631405084129460403813

theorem tailTrace_5220511 : CollatzResearch.WordTrace tailWord_5220511 prefixEnd_5220511 2680631405084129460403813 := by
  unfold tailWord_5220511
  simp only [CollatzResearch.WordTrace]
  refine ⟨190407678789987714140621387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126938452526658476093747591 190407678789987714140621387)
  ·
    refine ⟨285611518184981571210932081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190407678789987714140621387 285611518184981571210932081)
    ·
      refine ⟨214208638638736178408199061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 285611518184981571210932081 214208638638736178408199061)
      ·
        refine ⟨10041029936190758362884331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 214208638638736178408199061 10041029936190758362884331)
        ·
          refine ⟨15061544904286137544326497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10041029936190758362884331 15061544904286137544326497)
          ·
            refine ⟨11296158678214603158244873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15061544904286137544326497 11296158678214603158244873)
            ·
              refine ⟨8472119008660952368683655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11296158678214603158244873 8472119008660952368683655)
              ·
                refine ⟨12708178512991428553025483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8472119008660952368683655 12708178512991428553025483)
                ·
                  refine ⟨19062267769487142829538225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12708178512991428553025483 19062267769487142829538225)
                  ·
                    refine ⟨14296700827115357122153669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19062267769487142829538225 14296700827115357122153669)
                    ·
                      refine ⟨2680631405084129460403813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14296700827115357122153669 2680631405084129460403813)
                      ·
                        rfl

theorem cell23_5220511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_5220511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5220511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5220511 prefixEnd_5220511 := by exact prefixLift 5220511
  have htrace : WordTrace (prefixWord ++ tailWord_5220511) baseStart_5220511 baseEnd_5220511 := by
    simpa [prefixWord, tailWord_5220511, baseEnd_5220511] using wordTrace_append hprefix tailTrace_5220511
  have hstable : (prefixWord ++ tailWord_5220511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5220511).length < 2 ^ (prefixWord ++ tailWord_5220511).sum := by decide
  have hdescent : baseEnd_5220511 < baseStart_5220511 := by decide
  rcases family_descends (prefixWord ++ tailWord_5220511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5220517 : List Nat := [1, 3, 1, 2, 1, 3, 1, 2, 2, 7]
def baseStart_5220517 : Nat := 118140960795 + 5220517 * 2 ^ 59
def prefixEnd_5220517 : Nat := 4983230072969 + 3 ^ 40 * 5220517 * 2
def baseEnd_5220517 : Nat := 893544828656018812309595

theorem tailTrace_5220517 : CollatzResearch.WordTrace tailWord_5220517 prefixEnd_5220517 893544828656018812309595 := by
  unfold tailWord_5220517
  simp only [CollatzResearch.WordTrace]
  refine ⟨190407897627965977165339805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126938598418643984776893203 190407897627965977165339805)
  ·
    refine ⟨71402961610487241437002427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190407897627965977165339805 71402961610487241437002427)
    ·
      refine ⟨107104442415730862155503641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71402961610487241437002427 107104442415730862155503641)
      ·
        refine ⟨80328331811798146616627731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107104442415730862155503641 80328331811798146616627731)
        ·
          refine ⟨120492497717697219924941597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80328331811798146616627731 120492497717697219924941597)
          ·
            refine ⟨45184686644136457471853099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120492497717697219924941597 45184686644136457471853099)
            ·
              refine ⟨67777029966204686207779649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45184686644136457471853099 67777029966204686207779649)
              ·
                refine ⟨50832772474653514655834737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67777029966204686207779649 50832772474653514655834737)
                ·
                  refine ⟨38124579355990135991876053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50832772474653514655834737 38124579355990135991876053)
                  ·
                    refine ⟨893544828656018812309595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38124579355990135991876053 893544828656018812309595)
                    ·
                      rfl

theorem cell23_5220517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 7].length) (baseStart_5220517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5220517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5220517 prefixEnd_5220517 := by exact prefixLift 5220517
  have htrace : WordTrace (prefixWord ++ tailWord_5220517) baseStart_5220517 baseEnd_5220517 := by
    simpa [prefixWord, tailWord_5220517, baseEnd_5220517] using wordTrace_append hprefix tailTrace_5220517
  have hstable : (prefixWord ++ tailWord_5220517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5220517).length < 2 ^ (prefixWord ++ tailWord_5220517).sum := by decide
  have hdescent : baseEnd_5220517 < baseStart_5220517 := by decide
  rcases family_descends (prefixWord ++ tailWord_5220517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5220527 : List Nat := [1, 1, 2, 1, 2, 3, 1, 3, 2, 2, 5]
def baseStart_5220527 : Nat := 118140960795 + 5220527 * 2 ^ 59
def prefixEnd_5220527 : Nat := 4983230072969 + 3 ^ 40 * 5220527 * 2
def baseEnd_5220527 : Nat := 2680639620774601397803739

theorem tailTrace_5220527 : CollatzResearch.WordTrace tailWord_5220527 prefixEnd_5220527 2680639620774601397803739 := by
  unfold tailWord_5220527
  simp only [CollatzResearch.WordTrace]
  refine ⟨190408262357929748873203835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126938841571953165915469223 190408262357929748873203835)
  ·
    refine ⟨285612393536894623309805753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190408262357929748873203835 285612393536894623309805753)
    ·
      refine ⟨214209295152670967482354315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 285612393536894623309805753 214209295152670967482354315)
      ·
        refine ⟨321313942729006451223531473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214209295152670967482354315 321313942729006451223531473)
        ·
          refine ⟨240985457046754838417648605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 321313942729006451223531473 240985457046754838417648605)
          ·
            refine ⟨90369546392533064406618227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 240985457046754838417648605 90369546392533064406618227)
            ·
              refine ⟨135554319588799596609927341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90369546392533064406618227 135554319588799596609927341)
              ·
                refine ⟨50832869845799848728722753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 135554319588799596609927341 50832869845799848728722753)
                ·
                  refine ⟨38124652384349886546542065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50832869845799848728722753 38124652384349886546542065)
                  ·
                    refine ⟨28593489288262414909906549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38124652384349886546542065 28593489288262414909906549)
                    ·
                      refine ⟨2680639620774601397803739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28593489288262414909906549 2680639620774601397803739)
                      ·
                        rfl

theorem cell23_5220527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 2, 5].length) (baseStart_5220527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5220527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5220527 prefixEnd_5220527 := by exact prefixLift 5220527
  have htrace : WordTrace (prefixWord ++ tailWord_5220527) baseStart_5220527 baseEnd_5220527 := by
    simpa [prefixWord, tailWord_5220527, baseEnd_5220527] using wordTrace_append hprefix tailTrace_5220527
  have hstable : (prefixWord ++ tailWord_5220527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5220527).length < 2 ^ (prefixWord ++ tailWord_5220527).sum := by decide
  have hdescent : baseEnd_5220527 < baseStart_5220527 := by decide
  rcases family_descends (prefixWord ++ tailWord_5220527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5220532 : List Nat := [2, 5, 3, 1, 1, 1, 1, 3, 1, 1, 4]
def baseStart_5220532 : Nat := 118140960795 + 5220532 * 2 ^ 59
def prefixEnd_5220532 : Nat := 4983230072969 + 3 ^ 40 * 5220532 * 2
def baseEnd_5220532 : Nat := 2680642188177873878241217

theorem tailTrace_5220532 : CollatzResearch.WordTrace tailWord_5220532 prefixEnd_5220532 2680642188177873878241217 := by
  unfold tailWord_5220532
  simp only [CollatzResearch.WordTrace]
  refine ⟨95204222361455817363567925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126938963148607756484757233 95204222361455817363567925)
  ·
    refine ⟨8925395846386482877834493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 95204222361455817363567925 8925395846386482877834493)
    ·
      refine ⟨3347023442394931079187935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8925395846386482877834493 3347023442394931079187935)
      ·
        refine ⟨5020535163592396618781903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3347023442394931079187935 5020535163592396618781903)
        ·
          refine ⟨7530802745388594928172855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5020535163592396618781903 7530802745388594928172855)
          ·
            refine ⟨11296204118082892392259283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7530802745388594928172855 11296204118082892392259283)
            ·
              refine ⟨16944306177124338588388925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11296204118082892392259283 16944306177124338588388925)
              ·
                refine ⟨6354114816421626970645847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16944306177124338588388925 6354114816421626970645847)
                ·
                  refine ⟨9531172224632440455968771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6354114816421626970645847 9531172224632440455968771)
                  ·
                    refine ⟨14296758336948660683953157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9531172224632440455968771 14296758336948660683953157)
                    ·
                      refine ⟨2680642188177873878241217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14296758336948660683953157 2680642188177873878241217)
                      ·
                        rfl

theorem cell23_5220532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_5220532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5220532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5220532 prefixEnd_5220532 := by exact prefixLift 5220532
  have htrace : WordTrace (prefixWord ++ tailWord_5220532) baseStart_5220532 baseEnd_5220532 := by
    simpa [prefixWord, tailWord_5220532, baseEnd_5220532] using wordTrace_append hprefix tailTrace_5220532
  have hstable : (prefixWord ++ tailWord_5220532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5220532).length < 2 ^ (prefixWord ++ tailWord_5220532).sum := by decide
  have hdescent : baseEnd_5220532 < baseStart_5220532 := by decide
  rcases family_descends (prefixWord ++ tailWord_5220532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5220548 : List Nat := [2, 3, 3, 1, 2, 2, 1, 1, 4, 1, 3]
def baseStart_5220548 : Nat := 118140960795 + 5220548 * 2 ^ 59
def prefixEnd_5220548 : Nat := 4983230072969 + 3 ^ 40 * 5220548 * 2
def baseEnd_5220548 : Nat := 2680650403868345815641143

theorem tailTrace_5220548 : CollatzResearch.WordTrace tailWord_5220548 prefixEnd_5220548 2680650403868345815641143 := by
  unfold tailWord_5220548
  simp only [CollatzResearch.WordTrace]
  refine ⟨95204514145426834729859149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126939352193902446306478865 95204514145426834729859149)
  ·
    refine ⟨35701692804535063023697181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95204514145426834729859149 35701692804535063023697181)
    ·
      refine ⟨13388134801700648633886443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35701692804535063023697181 13388134801700648633886443)
      ·
        refine ⟨20082202202550972950829665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13388134801700648633886443 20082202202550972950829665)
        ·
          refine ⟨15061651651913229713122249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20082202202550972950829665 15061651651913229713122249)
          ·
            refine ⟨11296238738934922284841687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15061651651913229713122249 11296238738934922284841687)
            ·
              refine ⟨16944358108402383427262531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11296238738934922284841687 16944358108402383427262531)
              ·
                refine ⟨25416537162603575140893797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16944358108402383427262531 25416537162603575140893797)
                ·
                  refine ⟨4765600717988170338917587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25416537162603575140893797 4765600717988170338917587)
                  ·
                    refine ⟨7148401076982255508376381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4765600717988170338917587 7148401076982255508376381)
                    ·
                      refine ⟨2680650403868345815641143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7148401076982255508376381 2680650403868345815641143)
                      ·
                        rfl

theorem cell23_5220548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_5220548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5220548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5220548 prefixEnd_5220548 := by exact prefixLift 5220548
  have htrace : WordTrace (prefixWord ++ tailWord_5220548) baseStart_5220548 baseEnd_5220548 := by
    simpa [prefixWord, tailWord_5220548, baseEnd_5220548] using wordTrace_append hprefix tailTrace_5220548
  have hstable : (prefixWord ++ tailWord_5220548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5220548).length < 2 ^ (prefixWord ++ tailWord_5220548).sum := by decide
  have hdescent : baseEnd_5220548 < baseStart_5220548 := by decide
  rcases family_descends (prefixWord ++ tailWord_5220548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5220565 : List Nat := [1, 3, 2, 4, 3, 1, 1, 1, 1, 3, 3]
def baseStart_5220565 : Nat := 118140960795 + 5220565 * 2 ^ 59
def prefixEnd_5220565 : Nat := 4983230072969 + 3 ^ 40 * 5220565 * 2
def baseEnd_5220565 : Nat := 2680659133039472249128565

theorem tailTrace_5220565 : CollatzResearch.WordTrace tailWord_5220565 prefixEnd_5220565 2680659133039472249128565 := by
  unfold tailWord_5220565
  simp only [CollatzResearch.WordTrace]
  refine ⟨190409648331792081363087149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126939765554528054242058099 190409648331792081363087149)
  ·
    refine ⟨71403618124422030511157681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190409648331792081363087149 71403618124422030511157681)
    ·
      refine ⟨53552713593316522883368261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71403618124422030511157681 53552713593316522883368261)
      ·
        refine ⟨10041133798746848040631549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53552713593316522883368261 10041133798746848040631549)
        ·
          refine ⟨3765425174530068015236831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10041133798746848040631549 3765425174530068015236831)
          ·
            refine ⟨5648137761795102022855247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3765425174530068015236831 5648137761795102022855247)
            ·
              refine ⟨8472206642692653034282871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5648137761795102022855247 8472206642692653034282871)
              ·
                refine ⟨12708309964038979551424307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8472206642692653034282871 12708309964038979551424307)
                ·
                  refine ⟨19062464946058469327136461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12708309964038979551424307 19062464946058469327136461)
                  ·
                    refine ⟨7148424354771925997676173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19062464946058469327136461 7148424354771925997676173)
                    ·
                      refine ⟨2680659133039472249128565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7148424354771925997676173 2680659133039472249128565)
                      ·
                        rfl

theorem cell23_5220565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_5220565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5220565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5220565 prefixEnd_5220565 := by exact prefixLift 5220565
  have htrace : WordTrace (prefixWord ++ tailWord_5220565) baseStart_5220565 baseEnd_5220565 := by
    simpa [prefixWord, tailWord_5220565, baseEnd_5220565] using wordTrace_append hprefix tailTrace_5220565
  have hstable : (prefixWord ++ tailWord_5220565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5220565).length < 2 ^ (prefixWord ++ tailWord_5220565).sum := by decide
  have hdescent : baseEnd_5220565 < baseStart_5220565 := by decide
  rcases family_descends (prefixWord ++ tailWord_5220565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5220571 : List Nat := [1, 1, 1, 1, 1, 1, 1, 6, 6, 2, 2]
def baseStart_5220571 : Nat := 118140960795 + 5220571 * 2 ^ 59
def prefixEnd_5220571 : Nat := 4983230072969 + 3 ^ 40 * 5220571 * 2
def baseEnd_5220571 : Nat := 2680662213923399225653537

theorem tailTrace_5220571 : CollatzResearch.WordTrace tailWord_5220571 prefixEnd_5220571 2680662213923399225653537 := by
  unfold tailWord_5220571
  simp only [CollatzResearch.WordTrace]
  refine ⟨190409867169770344387805567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126939911446513562925203711 190409867169770344387805567)
  ·
    refine ⟨285614800754655516581708351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190409867169770344387805567 285614800754655516581708351)
    ·
      refine ⟨428422201131983274872562527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285614800754655516581708351 428422201131983274872562527)
      ·
        refine ⟨642633301697974912308843791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 428422201131983274872562527 642633301697974912308843791)
        ·
          refine ⟨963949952546962368463265687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 642633301697974912308843791 963949952546962368463265687)
          ·
            refine ⟨1445924928820443552694898531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 963949952546962368463265687 1445924928820443552694898531)
            ·
              refine ⟨2168887393230665329042347797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1445924928820443552694898531 2168887393230665329042347797)
              ·
                refine ⟨101666596557687437298860053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2168887393230665329042347797 101666596557687437298860053)
                ·
                  refine ⟨4765621713641598623384065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 101666596557687437298860053 4765621713641598623384065)
                  ·
                    refine ⟨3574216285231198967538049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4765621713641598623384065 3574216285231198967538049)
                    ·
                      refine ⟨2680662213923399225653537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3574216285231198967538049 2680662213923399225653537)
                      ·
                        rfl

theorem cell23_5220571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6, 2, 2].length) (baseStart_5220571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5220571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5220571 prefixEnd_5220571 := by exact prefixLift 5220571
  have htrace : WordTrace (prefixWord ++ tailWord_5220571) baseStart_5220571 baseEnd_5220571 := by
    simpa [prefixWord, tailWord_5220571, baseEnd_5220571] using wordTrace_append hprefix tailTrace_5220571
  have hstable : (prefixWord ++ tailWord_5220571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5220571).length < 2 ^ (prefixWord ++ tailWord_5220571).sum := by decide
  have hdescent : baseEnd_5220571 < baseStart_5220571 := by decide
  rcases family_descends (prefixWord ++ tailWord_5220571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5220661 : List Nat := [1, 3, 3, 1, 2, 1, 1, 4, 2, 1, 4]
def baseStart_5220661 : Nat := 118140960795 + 5220661 * 2 ^ 59
def prefixEnd_5220661 : Nat := 4983230072969 + 3 ^ 40 * 5220661 * 2
def baseEnd_5220661 : Nat := 2680708427182303873528123

theorem tailTrace_5220661 : CollatzResearch.WordTrace tailWord_5220661 prefixEnd_5220661 2680708427182303873528123 := by
  unfold tailWord_5220661
  simp only [CollatzResearch.WordTrace]
  refine ⟨190413149739444289758581837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126942099826296193172387891 190413149739444289758581837)
  ·
    refine ⟨71404931152291608659468189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190413149739444289758581837 71404931152291608659468189)
    ·
      refine ⟨26776849182109353247300571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71404931152291608659468189 26776849182109353247300571)
      ·
        refine ⟨40165273773164029870950857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26776849182109353247300571 40165273773164029870950857)
        ·
          refine ⟨30123955329873022403213143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40165273773164029870950857 30123955329873022403213143)
          ·
            refine ⟨45185932994809533604819715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30123955329873022403213143 45185932994809533604819715)
            ·
              refine ⟨67778899492214300407229573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45185932994809533604819715 67778899492214300407229573)
              ·
                refine ⟨12708543654790181326355545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67778899492214300407229573 12708543654790181326355545)
                ·
                  refine ⟨9531407741092635994766659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12708543654790181326355545 9531407741092635994766659)
                  ·
                    refine ⟨14297111611638953992149989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9531407741092635994766659 14297111611638953992149989)
                    ·
                      refine ⟨2680708427182303873528123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14297111611638953992149989 2680708427182303873528123)
                      ·
                        rfl

theorem cell23_5220661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_5220661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5220661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5220661 prefixEnd_5220661 := by exact prefixLift 5220661
  have htrace : WordTrace (prefixWord ++ tailWord_5220661) baseStart_5220661 baseEnd_5220661 := by
    simpa [prefixWord, tailWord_5220661, baseEnd_5220661] using wordTrace_append hprefix tailTrace_5220661
  have hstable : (prefixWord ++ tailWord_5220661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5220661).length < 2 ^ (prefixWord ++ tailWord_5220661).sum := by decide
  have hdescent : baseEnd_5220661 < baseStart_5220661 := by decide
  rcases family_descends (prefixWord ++ tailWord_5220661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5220671 : List Nat := [1, 1, 2, 2, 4, 1, 2, 3, 3, 4]
def baseStart_5220671 : Nat := 118140960795 + 5220671 * 2 ^ 59
def prefixEnd_5220671 : Nat := 4983230072969 + 3 ^ 40 * 5220671 * 2
def baseEnd_5220671 : Nat := 893571187329616278134359

theorem tailTrace_5220671 : CollatzResearch.WordTrace tailWord_5220671 prefixEnd_5220671 893571187329616278134359 := by
  unfold tailWord_5220671
  simp only [CollatzResearch.WordTrace]
  refine ⟨190413514469408061466445867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126942342979605374310963911 190413514469408061466445867)
  ·
    refine ⟨285620271704112092199668801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190413514469408061466445867 285620271704112092199668801)
    ·
      refine ⟨214215203778084069149751601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 285620271704112092199668801 214215203778084069149751601)
      ·
        refine ⟨160661402833563051862313701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214215203778084069149751601 160661402833563051862313701)
        ·
          refine ⟨30124013031293072224183819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 160661402833563051862313701 30124013031293072224183819)
          ·
            refine ⟨45186019546939608336275729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30124013031293072224183819 45186019546939608336275729)
            ·
              refine ⟨33889514660204706252206797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45186019546939608336275729 33889514660204706252206797)
              ·
                refine ⟨12708567997576764844577549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33889514660204706252206797 12708567997576764844577549)
                ·
                  refine ⟨4765712999091286816716581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12708567997576764844577549 4765712999091286816716581)
                  ·
                    refine ⟨893571187329616278134359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4765712999091286816716581 893571187329616278134359)
                    ·
                      rfl

theorem cell23_5220671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 3, 3, 4].length) (baseStart_5220671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5220671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5220671 prefixEnd_5220671 := by exact prefixLift 5220671
  have htrace : WordTrace (prefixWord ++ tailWord_5220671) baseStart_5220671 baseEnd_5220671 := by
    simpa [prefixWord, tailWord_5220671, baseEnd_5220671] using wordTrace_append hprefix tailTrace_5220671
  have hstable : (prefixWord ++ tailWord_5220671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5220671).length < 2 ^ (prefixWord ++ tailWord_5220671).sum := by decide
  have hdescent : baseEnd_5220671 < baseStart_5220671 := by decide
  rcases family_descends (prefixWord ++ tailWord_5220671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5220748 : List Nat := [2, 2, 1, 2, 1, 5, 2, 2, 1, 5]
def baseStart_5220748 : Nat := 118140960795 + 5220748 * 2 ^ 59
def prefixEnd_5220748 : Nat := 4983230072969 + 3 ^ 40 * 5220748 * 2
def baseEnd_5220748 : Nat := 893584366666415011046741

theorem tailTrace_5220748 : CollatzResearch.WordTrace tailWord_5220748 prefixEnd_5220748 893584366666415011046741 := by
  unfold tailWord_5220748
  simp only [CollatzResearch.WordTrace]
  refine ⟨95208161445064551808499449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126944215260086069077999265 95208161445064551808499449)
  ·
    refine ⟨71406121083798413856374587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95208161445064551808499449 71406121083798413856374587)
    ·
      refine ⟨107109181625697620784561881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71406121083798413856374587 107109181625697620784561881)
      ·
        refine ⟨80331886219273215588421411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107109181625697620784561881 80331886219273215588421411)
        ·
          refine ⟨120497829328909823382632117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80331886219273215588421411 120497829328909823382632117)
          ·
            refine ⟨11296671499585295942121761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 120497829328909823382632117 11296671499585295942121761)
            ·
              refine ⟨8472503624688971956591321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11296671499585295942121761 8472503624688971956591321)
              ·
                refine ⟨6354377718516728967443491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8472503624688971956591321 6354377718516728967443491)
                ·
                  refine ⟨9531566577775093451165237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6354377718516728967443491 9531566577775093451165237)
                  ·
                    refine ⟨893584366666415011046741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9531566577775093451165237 893584366666415011046741)
                    ·
                      rfl

theorem cell23_5220748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 2, 1, 5].length) (baseStart_5220748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5220748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5220748 prefixEnd_5220748 := by exact prefixLift 5220748
  have htrace : WordTrace (prefixWord ++ tailWord_5220748) baseStart_5220748 baseEnd_5220748 := by
    simpa [prefixWord, tailWord_5220748, baseEnd_5220748] using wordTrace_append hprefix tailTrace_5220748
  have hstable : (prefixWord ++ tailWord_5220748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5220748).length < 2 ^ (prefixWord ++ tailWord_5220748).sum := by decide
  have hdescent : baseEnd_5220748 < baseStart_5220748 := by decide
  rcases family_descends (prefixWord ++ tailWord_5220748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5220761 : List Nat := [1, 2, 1, 2, 1, 4, 1, 1, 6, 4]
def baseStart_5220761 : Nat := 118140960795 + 5220761 * 2 ^ 59
def prefixEnd_5220761 : Nat := 4983230072969 + 3 ^ 40 * 5220761 * 2
def baseEnd_5220761 : Nat := 893586591749251160759221

theorem tailTrace_5220761 : CollatzResearch.WordTrace tailWord_5220761 prefixEnd_5220761 893586591749251160759221 := by
  unfold tailWord_5220761
  simp only [CollatzResearch.WordTrace]
  refine ⟨190416797039082006837222137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126944531359388004558148091 190416797039082006837222137)
  ·
    refine ⟨142812597779311505127916603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190416797039082006837222137 142812597779311505127916603)
    ·
      refine ⟨214218896668967257691874905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142812597779311505127916603 214218896668967257691874905)
      ·
        refine ⟨160664172501725443268906179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214218896668967257691874905 160664172501725443268906179)
        ·
          refine ⟨240996258752588164903359269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160664172501725443268906179 240996258752588164903359269)
          ·
            refine ⟨45186798516110280919379863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 240996258752588164903359269 45186798516110280919379863)
            ·
              refine ⟨67780197774165421379069795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45186798516110280919379863 67780197774165421379069795)
              ·
                refine ⟨101670296661248132068604693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67780197774165421379069795 101670296661248132068604693)
                ·
                  refine ⟨4765795155996006190715845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 101670296661248132068604693 4765795155996006190715845)
                  ·
                    refine ⟨893586591749251160759221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4765795155996006190715845 893586591749251160759221)
                    ·
                      rfl

theorem cell23_5220761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 6, 4].length) (baseStart_5220761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5220761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5220761 prefixEnd_5220761 := by exact prefixLift 5220761
  have htrace : WordTrace (prefixWord ++ tailWord_5220761) baseStart_5220761 baseEnd_5220761 := by
    simpa [prefixWord, tailWord_5220761, baseEnd_5220761] using wordTrace_append hprefix tailTrace_5220761
  have hstable : (prefixWord ++ tailWord_5220761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5220761).length < 2 ^ (prefixWord ++ tailWord_5220761).sum := by decide
  have hdescent : baseEnd_5220761 < baseStart_5220761 := by decide
  rcases family_descends (prefixWord ++ tailWord_5220761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5220762 : List Nat := [3, 1, 1, 4, 1, 2, 3, 3, 1, 1, 3]
def baseStart_5220762 : Nat := 118140960795 + 5220762 * 2 ^ 59
def prefixEnd_5220762 : Nat := 4983230072969 + 3 ^ 40 * 5220762 * 2
def baseEnd_5220762 : Nat := 2680760288728407978365159

theorem tailTrace_5220762 : CollatzResearch.WordTrace tailWord_5220762 prefixEnd_5220762 2680760288728407978365159 := by
  unfold tailWord_5220762
  simp only [CollatzResearch.WordTrace]
  refine ⟨47604208378019596002002135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126944555674718922672005693 47604208378019596002002135)
  ·
    refine ⟨71406312567029394003003203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47604208378019596002002135 71406312567029394003003203)
    ·
      refine ⟨107109468850544091004504805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71406312567029394003003203 107109468850544091004504805)
      ·
        refine ⟨20083025409477017063344651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107109468850544091004504805 20083025409477017063344651)
        ·
          refine ⟨30124538114215525595016977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20083025409477017063344651 30124538114215525595016977)
          ·
            refine ⟨22593403585661644196262733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30124538114215525595016977 22593403585661644196262733)
            ·
              refine ⟨8472526344623116573598525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22593403585661644196262733 8472526344623116573598525)
              ·
                refine ⟨3177197379233668715099447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8472526344623116573598525 3177197379233668715099447)
                ·
                  refine ⟨4765796068850503072649171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3177197379233668715099447 4765796068850503072649171)
                  ·
                    refine ⟨7148694103275754608973757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4765796068850503072649171 7148694103275754608973757)
                    ·
                      refine ⟨2680760288728407978365159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7148694103275754608973757 2680760288728407978365159)
                      ·
                        rfl

theorem cell23_5220762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 3, 1, 1, 3].length) (baseStart_5220762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5220762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5220762 prefixEnd_5220762 := by exact prefixLift 5220762
  have htrace : WordTrace (prefixWord ++ tailWord_5220762) baseStart_5220762 baseEnd_5220762 := by
    simpa [prefixWord, tailWord_5220762, baseEnd_5220762] using wordTrace_append hprefix tailTrace_5220762
  have hstable : (prefixWord ++ tailWord_5220762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5220762).length < 2 ^ (prefixWord ++ tailWord_5220762).sum := by decide
  have hdescent : baseEnd_5220762 < baseStart_5220762 := by decide
  rcases family_descends (prefixWord ++ tailWord_5220762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5220768 : List Nat := [2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 4]
def baseStart_5220768 : Nat := 118140960795 + 5220768 * 2 ^ 59
def prefixEnd_5220768 : Nat := 4983230072969 + 3 ^ 40 * 5220768 * 2
def baseEnd_5220768 : Nat := 2680763369612334954890131

theorem tailTrace_5220768 : CollatzResearch.WordTrace tailWord_5220768 prefixEnd_5220768 2680763369612334954890131 := by
  unfold tailWord_5220768
  simp only [CollatzResearch.WordTrace]
  refine ⟨95208526175028323516363479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126944701566704431355151305 95208526175028323516363479)
  ·
    refine ⟨142812789262542485274545219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95208526175028323516363479 142812789262542485274545219)
    ·
      refine ⟨214219183893813727911817829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142812789262542485274545219 214219183893813727911817829)
      ·
        refine ⟨40166096980090073983465843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 214219183893813727911817829 40166096980090073983465843)
        ·
          refine ⟨60249145470135110975198765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40166096980090073983465843 60249145470135110975198765)
          ·
            refine ⟨22593429551300666615699537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60249145470135110975198765 22593429551300666615699537)
            ·
              refine ⟨16945072163475499961774653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22593429551300666615699537 16945072163475499961774653)
              ·
                refine ⟨6354402061303312485665495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16945072163475499961774653 6354402061303312485665495)
                ·
                  refine ⟨9531603091954968728498243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6354402061303312485665495 9531603091954968728498243)
                  ·
                    refine ⟨14297404637932453092747365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9531603091954968728498243 14297404637932453092747365)
                    ·
                      refine ⟨2680763369612334954890131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14297404637932453092747365 2680763369612334954890131)
                      ·
                        rfl

theorem cell23_5220768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 4].length) (baseStart_5220768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5220768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5220768 prefixEnd_5220768 := by exact prefixLift 5220768
  have htrace : WordTrace (prefixWord ++ tailWord_5220768) baseStart_5220768 baseEnd_5220768 := by
    simpa [prefixWord, tailWord_5220768, baseEnd_5220768] using wordTrace_append hprefix tailTrace_5220768
  have hstable : (prefixWord ++ tailWord_5220768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5220768).length < 2 ^ (prefixWord ++ tailWord_5220768).sum := by decide
  have hdescent : baseEnd_5220768 < baseStart_5220768 := by decide
  rcases family_descends (prefixWord ++ tailWord_5220768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5220771 : List Nat := [1, 1, 1, 4, 1, 4, 1, 3, 1, 1, 5]
def baseStart_5220771 : Nat := 118140960795 + 5220771 * 2 ^ 59
def prefixEnd_5220771 : Nat := 4983230072969 + 3 ^ 40 * 5220771 * 2
def baseEnd_5220771 : Nat := 2680764910054298443152617

theorem tailTrace_5220771 : CollatzResearch.WordTrace tailWord_5220771 prefixEnd_5220771 2680764910054298443152617 := by
  unfold tailWord_5220771
  simp only [CollatzResearch.WordTrace]
  refine ⟨190417161769045778545086167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126944774512697185696724111 190417161769045778545086167)
  ·
    refine ⟨285625742653568667817629251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190417161769045778545086167 285625742653568667817629251)
    ·
      refine ⟨428438613980353001726443877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285625742653568667817629251 428438613980353001726443877)
      ·
        refine ⟨80332240121316187823708227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 428438613980353001726443877 80332240121316187823708227)
        ·
          refine ⟨120498360181974281735562341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80332240121316187823708227 120498360181974281735562341)
          ·
            refine ⟨22593442534120177825417939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 120498360181974281735562341 22593442534120177825417939)
            ·
              refine ⟨33890163801180266738126909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22593442534120177825417939 33890163801180266738126909)
              ·
                refine ⟨12708811425442600026797591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33890163801180266738126909 12708811425442600026797591)
                ·
                  refine ⟨19063217138163900040196387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12708811425442600026797591 19063217138163900040196387)
                  ·
                    refine ⟨28594825707245850060294581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19063217138163900040196387 28594825707245850060294581)
                    ·
                      refine ⟨2680764910054298443152617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28594825707245850060294581 2680764910054298443152617)
                      ·
                        rfl

theorem cell23_5220771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 3, 1, 1, 5].length) (baseStart_5220771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5220771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5220771 prefixEnd_5220771 := by exact prefixLift 5220771
  have htrace : WordTrace (prefixWord ++ tailWord_5220771) baseStart_5220771 baseEnd_5220771 := by
    simpa [prefixWord, tailWord_5220771, baseEnd_5220771] using wordTrace_append hprefix tailTrace_5220771
  have hstable : (prefixWord ++ tailWord_5220771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5220771).length < 2 ^ (prefixWord ++ tailWord_5220771).sum := by decide
  have hdescent : baseEnd_5220771 < baseStart_5220771 := by decide
  rcases family_descends (prefixWord ++ tailWord_5220771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5220791 : List Nat := [1, 1, 3, 1, 3, 4, 2, 8]
def baseStart_5220791 : Nat := 118140960795 + 5220791 * 2 ^ 59
def prefixEnd_5220791 : Nat := 4983230072969 + 3 ^ 40 * 5220791 * 2
def baseEnd_5220791 : Nat := 99287969617310680181575

theorem tailTrace_5220791 : CollatzResearch.WordTrace tailWord_5220791 prefixEnd_5220791 99287969617310680181575 := by
  unfold tailWord_5220791
  simp only [CollatzResearch.WordTrace]
  refine ⟨190417891228973321960814227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126945260819315547973876151 190417891228973321960814227)
  ·
    refine ⟨285626836843459982941221341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190417891228973321960814227 285626836843459982941221341)
    ·
      refine ⟨107110063816297493602958003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 285626836843459982941221341 107110063816297493602958003)
      ·
        refine ⟨160665095724446240404437005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107110063816297493602958003 160665095724446240404437005)
        ·
          refine ⟨60249410896667340151663877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 160665095724446240404437005 60249410896667340151663877)
          ·
            refine ⟨11296764543125126278436977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60249410896667340151663877 11296764543125126278436977)
            ·
              refine ⟨8472573407343844708827733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11296764543125126278436977 8472573407343844708827733)
              ·
                refine ⟨99287969617310680181575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8472573407343844708827733 99287969617310680181575)
                ·
                  rfl

theorem cell23_5220791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 8].length) (baseStart_5220791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5220791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5220791 prefixEnd_5220791 := by exact prefixLift 5220791
  have htrace : WordTrace (prefixWord ++ tailWord_5220791) baseStart_5220791 baseEnd_5220791 := by
    simpa [prefixWord, tailWord_5220791, baseEnd_5220791] using wordTrace_append hprefix tailTrace_5220791
  have hstable : (prefixWord ++ tailWord_5220791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5220791).length < 2 ^ (prefixWord ++ tailWord_5220791).sum := by decide
  have hdescent : baseEnd_5220791 < baseStart_5220791 := by decide
  rcases family_descends (prefixWord ++ tailWord_5220791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5220851 : List Nat := [1, 1, 1, 2, 2, 2, 5, 1, 2, 6]
def baseStart_5220851 : Nat := 118140960795 + 5220851 * 2 ^ 59
def prefixEnd_5220851 : Nat := 4983230072969 + 3 ^ 40 * 5220851 * 2
def baseEnd_5220851 : Nat := 893601996168886043384083

theorem tailTrace_5220851 : CollatzResearch.WordTrace tailWord_5220851 prefixEnd_5220851 893601996168886043384083 := by
  unfold tailWord_5220851
  simp only [CollatzResearch.WordTrace]
  refine ⟨190420079608755952207998407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126946719739170634805332271 190420079608755952207998407)
  ·
    refine ⟨285630119413133928311997611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190420079608755952207998407 285630119413133928311997611)
    ·
      refine ⟨428445179119700892467996417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285630119413133928311997611 428445179119700892467996417)
      ·
        refine ⟨321333884339775669350997313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 428445179119700892467996417 321333884339775669350997313)
        ·
          refine ⟨241000413254831752013247985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 321333884339775669350997313 241000413254831752013247985)
          ·
            refine ⟨180750309941123814009935989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 241000413254831752013247985 180750309941123814009935989)
            ·
              refine ⟨16945341556980357563431499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 180750309941123814009935989 16945341556980357563431499)
              ·
                refine ⟨25418012335470536345147249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16945341556980357563431499 25418012335470536345147249)
                ·
                  refine ⟨19063509251602902258860437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25418012335470536345147249 19063509251602902258860437)
                  ·
                    refine ⟨893601996168886043384083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19063509251602902258860437 893601996168886043384083)
                    ·
                      rfl

theorem cell23_5220851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 2, 6].length) (baseStart_5220851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5220851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5220851 prefixEnd_5220851 := by exact prefixLift 5220851
  have htrace : WordTrace (prefixWord ++ tailWord_5220851) baseStart_5220851 baseEnd_5220851 := by
    simpa [prefixWord, tailWord_5220851, baseEnd_5220851] using wordTrace_append hprefix tailTrace_5220851
  have hstable : (prefixWord ++ tailWord_5220851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5220851).length < 2 ^ (prefixWord ++ tailWord_5220851).sum := by decide
  have hdescent : baseEnd_5220851 < baseStart_5220851 := by decide
  rcases family_descends (prefixWord ++ tailWord_5220851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5220870 : List Nat := [6, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2]
def baseStart_5220870 : Nat := 118140960795 + 5220870 * 2 ^ 59
def prefixEnd_5220870 : Nat := 4983230072969 + 3 ^ 40 * 5220870 * 2
def baseEnd_5220870 : Nat := 2680815744639093555814663

theorem tailTrace_5220870 : CollatzResearch.WordTrace tailWord_5220870 prefixEnd_5220870 2680815744639093555814663 := by
  unfold tailWord_5220870
  simp only [CollatzResearch.WordTrace]
  refine ⟨5950649143615222451654377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 126947181730458078968626709 5950649143615222451654377)
  ·
    refine ⟨4462986857711416838740783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5950649143615222451654377 4462986857711416838740783)
    ·
      refine ⟨6694480286567125258111175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4462986857711416838740783 6694480286567125258111175)
      ·
        refine ⟨10041720429850687887166763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6694480286567125258111175 10041720429850687887166763)
        ·
          refine ⟨15062580644776031830750145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10041720429850687887166763 15062580644776031830750145)
          ·
            refine ⟨11296935483582023873062609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15062580644776031830750145 11296935483582023873062609)
            ·
              refine ⟨8472701612686517904796957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11296935483582023873062609 8472701612686517904796957)
              ·
                refine ⟨3177263104757444214298859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8472701612686517904796957 3177263104757444214298859)
                ·
                  refine ⟨4765894657136166321448289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3177263104757444214298859 4765894657136166321448289)
                  ·
                    refine ⟨3574420992852124741086217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4765894657136166321448289 3574420992852124741086217)
                    ·
                      refine ⟨2680815744639093555814663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3574420992852124741086217 2680815744639093555814663)
                      ·
                        rfl

theorem cell23_5220870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_5220870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5220870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5220870 prefixEnd_5220870 := by exact prefixLift 5220870
  have htrace : WordTrace (prefixWord ++ tailWord_5220870) baseStart_5220870 baseEnd_5220870 := by
    simpa [prefixWord, tailWord_5220870, baseEnd_5220870] using wordTrace_append hprefix tailTrace_5220870
  have hstable : (prefixWord ++ tailWord_5220870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5220870).length < 2 ^ (prefixWord ++ tailWord_5220870).sum := by decide
  have hdescent : baseEnd_5220870 < baseStart_5220870 := by decide
  rcases family_descends (prefixWord ++ tailWord_5220870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5220875 : List Nat := [1, 1, 1, 1, 7, 1, 2, 2, 1, 4, 2]
def baseStart_5220875 : Nat := 118140960795 + 5220875 * 2 ^ 59
def prefixEnd_5220875 : Nat := 4983230072969 + 3 ^ 40 * 5220875 * 2
def baseEnd_5220875 : Nat := 2680818312042366036252139

theorem tailTrace_5220875 : CollatzResearch.WordTrace tailWord_5220875 prefixEnd_5220875 2680818312042366036252139 := by
  unfold tailWord_5220875
  simp only [CollatzResearch.WordTrace]
  refine ⟨190420954960669004306872079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126947303307112669537914719 190420954960669004306872079)
  ·
    refine ⟨285631432441003506460308119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190420954960669004306872079 285631432441003506460308119)
    ·
      refine ⟨428447148661505259690462179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285631432441003506460308119 428447148661505259690462179)
      ·
        refine ⟨642670722992257889535693269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 428447148661505259690462179 642670722992257889535693269)
        ·
          refine ⟨15062595070131044285992811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 642670722992257889535693269 15062595070131044285992811)
          ·
            refine ⟨22593892605196566428989217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15062595070131044285992811 22593892605196566428989217)
            ·
              refine ⟨16945419453897424821741913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22593892605196566428989217 16945419453897424821741913)
              ·
                refine ⟨12709064590423068616306435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16945419453897424821741913 12709064590423068616306435)
                ·
                  refine ⟨19063596885634602924459653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12709064590423068616306435 19063596885634602924459653)
                  ·
                    refine ⟨3574424416056488048336185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19063596885634602924459653 3574424416056488048336185)
                    ·
                      refine ⟨2680818312042366036252139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3574424416056488048336185 2680818312042366036252139)
                      ·
                        rfl

theorem cell23_5220875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 2, 1, 4, 2].length) (baseStart_5220875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5220875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5220875 prefixEnd_5220875 := by exact prefixLift 5220875
  have htrace : WordTrace (prefixWord ++ tailWord_5220875) baseStart_5220875 baseEnd_5220875 := by
    simpa [prefixWord, tailWord_5220875, baseEnd_5220875] using wordTrace_append hprefix tailTrace_5220875
  have hstable : (prefixWord ++ tailWord_5220875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5220875).length < 2 ^ (prefixWord ++ tailWord_5220875).sum := by decide
  have hdescent : baseEnd_5220875 < baseStart_5220875 := by decide
  rcases family_descends (prefixWord ++ tailWord_5220875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5220888 : List Nat := [2, 1, 2, 3, 3, 1, 1, 2, 2, 2, 4]
def baseStart_5220888 : Nat := 118140960795 + 5220888 * 2 ^ 59
def prefixEnd_5220888 : Nat := 4983230072969 + 3 ^ 40 * 5220888 * 2
def baseEnd_5220888 : Nat := 2680824987290874485389579

theorem tailTrace_5220888 : CollatzResearch.WordTrace tailWord_5220888 prefixEnd_5220888 2680824987290874485389579 := by
  unfold tailWord_5220888
  simp only [CollatzResearch.WordTrace]
  refine ⟨95210714554810953763547659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126947619406414605018063545 95210714554810953763547659)
  ·
    refine ⟨142816071832216430645321489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95210714554810953763547659 142816071832216430645321489)
    ·
      refine ⟨107112053874162322983991117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142816071832216430645321489 107112053874162322983991117)
      ·
        refine ⟨40167020202810871118996669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107112053874162322983991117 40167020202810871118996669)
        ·
          refine ⟨15062632576054076669623751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40167020202810871118996669 15062632576054076669623751)
          ·
            refine ⟨22593948864081115004435627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15062632576054076669623751 22593948864081115004435627)
            ·
              refine ⟨33890923296121672506653441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22593948864081115004435627 33890923296121672506653441)
              ·
                refine ⟨25418192472091254379990081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33890923296121672506653441 25418192472091254379990081)
                ·
                  refine ⟨19063644354068440784992561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25418192472091254379990081 19063644354068440784992561)
                  ·
                    refine ⟨14297733265551330588744421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19063644354068440784992561 14297733265551330588744421)
                    ·
                      refine ⟨2680824987290874485389579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14297733265551330588744421 2680824987290874485389579)
                      ·
                        rfl

theorem cell23_5220888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_5220888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5220888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5220888 prefixEnd_5220888 := by exact prefixLift 5220888
  have htrace : WordTrace (prefixWord ++ tailWord_5220888) baseStart_5220888 baseEnd_5220888 := by
    simpa [prefixWord, tailWord_5220888, baseEnd_5220888] using wordTrace_append hprefix tailTrace_5220888
  have hstable : (prefixWord ++ tailWord_5220888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5220888).length < 2 ^ (prefixWord ++ tailWord_5220888).sum := by decide
  have hdescent : baseEnd_5220888 < baseStart_5220888 := by decide
  rcases family_descends (prefixWord ++ tailWord_5220888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5220892 : List Nat := [2, 2, 3, 1, 2, 3, 1, 1, 4, 2, 2]
def baseStart_5220892 : Nat := 118140960795 + 5220892 * 2 ^ 59
def prefixEnd_5220892 : Nat := 4983230072969 + 3 ^ 40 * 5220892 * 2
def baseEnd_5220892 : Nat := 2680827041213492469739561

theorem tailTrace_5220892 : CollatzResearch.WordTrace tailWord_5220892 prefixEnd_5220892 2680827041213492469739561 := by
  unfold tailWord_5220892
  simp only [CollatzResearch.WordTrace]
  refine ⟨95210787500803708105120465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126947716667738277473493953 95210787500803708105120465)
  ·
    refine ⟨71408090625602781078840349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95210787500803708105120465 71408090625602781078840349)
    ·
      refine ⟨26778033984601042904565131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71408090625602781078840349 26778033984601042904565131)
      ·
        refine ⟨40167050976901564356847697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26778033984601042904565131 40167050976901564356847697)
        ·
          refine ⟨30125288232676173267635773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40167050976901564356847697 30125288232676173267635773)
          ·
            refine ⟨11296983087253564975363415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30125288232676173267635773 11296983087253564975363415)
            ·
              refine ⟨16945474630880347463045123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11296983087253564975363415 16945474630880347463045123)
              ·
                refine ⟨25418211946320521194567685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16945474630880347463045123 25418211946320521194567685)
                ·
                  refine ⟨4765914739935097723981441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25418211946320521194567685 4765914739935097723981441)
                  ·
                    refine ⟨3574436054951323292986081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4765914739935097723981441 3574436054951323292986081)
                    ·
                      refine ⟨2680827041213492469739561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3574436054951323292986081 2680827041213492469739561)
                      ·
                        rfl

theorem cell23_5220892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 4, 2, 2].length) (baseStart_5220892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5220892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5220892 prefixEnd_5220892 := by exact prefixLift 5220892
  have htrace : WordTrace (prefixWord ++ tailWord_5220892) baseStart_5220892 baseEnd_5220892 := by
    simpa [prefixWord, tailWord_5220892, baseEnd_5220892] using wordTrace_append hprefix tailTrace_5220892
  have hstable : (prefixWord ++ tailWord_5220892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5220892).length < 2 ^ (prefixWord ++ tailWord_5220892).sum := by decide
  have hdescent : baseEnd_5220892 < baseStart_5220892 := by decide
  rcases family_descends (prefixWord ++ tailWord_5220892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5220971 : List Nat := [1, 1, 1, 1, 2, 2, 1, 4, 10]
def baseStart_5220971 : Nat := 118140960795 + 5220971 * 2 ^ 59
def prefixEnd_5220971 : Nat := 4983230072969 + 3 ^ 40 * 5220971 * 2
def baseEnd_5220971 : Nat := 297874178465021962294633

theorem tailTrace_5220971 : CollatzResearch.WordTrace tailWord_5220971 prefixEnd_5220971 297874178465021962294633 := by
  unfold tailWord_5220971
  simp only [CollatzResearch.WordTrace]
  refine ⟨190424456368321212702366767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126949637578880808468244511 190424456368321212702366767)
  ·
    refine ⟨285636684552481819053550151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190424456368321212702366767 285636684552481819053550151)
    ·
      refine ⟨428455026828722728580325227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285636684552481819053550151 428455026828722728580325227)
      ·
        refine ⟨642682540243084092870487841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 428455026828722728580325227 642682540243084092870487841)
        ·
          refine ⟨482011905182313069652865881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 642682540243084092870487841 482011905182313069652865881)
          ·
            refine ⟨361508928886734802239649411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 482011905182313069652865881 361508928886734802239649411)
            ·
              refine ⟨542263393330102203359474117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 361508928886734802239649411 542263393330102203359474117)
              ·
                refine ⟨101674386249394163129901397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 542263393330102203359474117 101674386249394163129901397)
                ·
                  refine ⟨297874178465021962294633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 101674386249394163129901397 297874178465021962294633)
                  ·
                    rfl

theorem cell23_5220971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 10].length) (baseStart_5220971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5220971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5220971 prefixEnd_5220971 := by exact prefixLift 5220971
  have htrace : WordTrace (prefixWord ++ tailWord_5220971) baseStart_5220971 baseEnd_5220971 := by
    simpa [prefixWord, tailWord_5220971, baseEnd_5220971] using wordTrace_append hprefix tailTrace_5220971
  have hstable : (prefixWord ++ tailWord_5220971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5220971).length < 2 ^ (prefixWord ++ tailWord_5220971).sum := by decide
  have hdescent : baseEnd_5220971 < baseStart_5220971 := by decide
  rcases family_descends (prefixWord ++ tailWord_5220971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5220985 : List Nat := [1, 2, 1, 3, 3, 2, 1, 3, 2, 2, 3]
def baseStart_5220985 : Nat := 118140960795 + 5220985 * 2 ^ 59
def prefixEnd_5220985 : Nat := 4983230072969 + 3 ^ 40 * 5220985 * 2
def baseEnd_5220985 : Nat := 2680874794914360605876633

theorem tailTrace_5220985 : CollatzResearch.WordTrace tailWord_5220985 prefixEnd_5220985 2680874794914360605876633 := by
  unfold tailWord_5220985
  simp only [CollatzResearch.WordTrace]
  refine ⟨190424966990270493093376409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126949977993513662062250939 190424966990270493093376409)
  ·
    refine ⟨142818725242702869820032307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190424966990270493093376409 142818725242702869820032307)
    ·
      refine ⟨214228087864054304730048461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142818725242702869820032307 214228087864054304730048461)
      ·
        refine ⟨80335532949020364273768173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 214228087864054304730048461 80335532949020364273768173)
        ·
          refine ⟨30125824855882636602663065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80335532949020364273768173 30125824855882636602663065)
          ·
            refine ⟨22594368641911977451997299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30125824855882636602663065 22594368641911977451997299)
            ·
              refine ⟨33891552962867966177995949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22594368641911977451997299 33891552962867966177995949)
              ·
                refine ⟨12709332361075487316748481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33891552962867966177995949 12709332361075487316748481)
                ·
                  refine ⟨9531999270806615487561361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12709332361075487316748481 9531999270806615487561361)
                  ·
                    refine ⟨7148999453104961615671021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9531999270806615487561361 7148999453104961615671021)
                    ·
                      refine ⟨2680874794914360605876633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7148999453104961615671021 2680874794914360605876633)
                      ·
                        rfl

theorem cell23_5220985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 3, 2, 2, 3].length) (baseStart_5220985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5220985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5220985 prefixEnd_5220985 := by exact prefixLift 5220985
  have htrace : WordTrace (prefixWord ++ tailWord_5220985) baseStart_5220985 baseEnd_5220985 := by
    simpa [prefixWord, tailWord_5220985, baseEnd_5220985] using wordTrace_append hprefix tailTrace_5220985
  have hstable : (prefixWord ++ tailWord_5220985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5220985).length < 2 ^ (prefixWord ++ tailWord_5220985).sum := by decide
  have hdescent : baseEnd_5220985 < baseStart_5220985 := by decide
  rcases family_descends (prefixWord ++ tailWord_5220985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5221028 : List Nat := [2, 3, 1, 2, 2, 1, 1, 1, 2, 1, 7]
def baseStart_5221028 : Nat := 118140960795 + 5221028 * 2 ^ 59
def prefixEnd_5221028 : Nat := 4983230072969 + 3 ^ 40 * 5221028 * 2
def baseEnd_5221028 : Nat := 2680896874582503937638935

theorem tailTrace_5221028 : CollatzResearch.WordTrace tailWord_5221028 prefixEnd_5221028 2680896874582503937638935 := by
  unfold tailWord_5221028
  simp only [CollatzResearch.WordTrace]
  refine ⟨95213267664557355718595869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126951023552743140958127825 95213267664557355718595869)
  ·
    refine ⟨35704975374209008394473451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95213267664557355718595869 35704975374209008394473451)
    ·
      refine ⟨53557463061313512591710177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35704975374209008394473451 53557463061313512591710177)
      ·
        refine ⟨40168097295985134443782633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53557463061313512591710177 40168097295985134443782633)
        ·
          refine ⟨30126072971988850832836975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40168097295985134443782633 30126072971988850832836975)
          ·
            refine ⟨45189109457983276249255463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30126072971988850832836975 45189109457983276249255463)
            ·
              refine ⟨67783664186974914373883195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45189109457983276249255463 67783664186974914373883195)
              ·
                refine ⟨101675496280462371560824793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67783664186974914373883195 101675496280462371560824793)
                ·
                  refine ⟨76256622210346778670618595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101675496280462371560824793 76256622210346778670618595)
                  ·
                    refine ⟨114384933315520168005927893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 76256622210346778670618595 114384933315520168005927893)
                    ·
                      refine ⟨2680896874582503937638935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 114384933315520168005927893 2680896874582503937638935)
                      ·
                        rfl

theorem cell23_5221028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_5221028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5221028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5221028 prefixEnd_5221028 := by exact prefixLift 5221028
  have htrace : WordTrace (prefixWord ++ tailWord_5221028) baseStart_5221028 baseEnd_5221028 := by
    simpa [prefixWord, tailWord_5221028, baseEnd_5221028] using wordTrace_append hprefix tailTrace_5221028
  have hstable : (prefixWord ++ tailWord_5221028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5221028).length < 2 ^ (prefixWord ++ tailWord_5221028).sum := by decide
  have hdescent : baseEnd_5221028 < baseStart_5221028 := by decide
  rcases family_descends (prefixWord ++ tailWord_5221028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5221089 : List Nat := [1, 2, 3, 1, 4, 1, 2, 2, 3, 2, 2]
def baseStart_5221089 : Nat := 118140960795 + 5221089 * 2 ^ 59
def prefixEnd_5221089 : Nat := 4983230072969 + 3 ^ 40 * 5221089 * 2
def baseEnd_5221089 : Nat := 2680928196902428198976155

theorem tailTrace_5221089 : CollatzResearch.WordTrace tailWord_5221089 prefixEnd_5221089 2680928196902428198976155 := by
  unfold tailWord_5221089
  simp only [CollatzResearch.WordTrace]
  refine ⟨190428760181893718855162321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126952506787929145903441547 190428760181893718855162321)
  ·
    refine ⟨142821570136420289141371741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190428760181893718855162321 142821570136420289141371741)
    ·
      refine ⟨53558088801157608428014403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142821570136420289141371741 53558088801157608428014403)
      ·
        refine ⟨80337133201736412642021605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53558088801157608428014403 80337133201736412642021605)
        ·
          refine ⟨15063212475325577370379051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80337133201736412642021605 15063212475325577370379051)
          ·
            refine ⟨22594818712988366055568577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15063212475325577370379051 22594818712988366055568577)
            ·
              refine ⟨16946114034741274541676433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22594818712988366055568577 16946114034741274541676433)
              ·
                refine ⟨12709585526055955906257325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16946114034741274541676433 12709585526055955906257325)
                ·
                  refine ⟨4766094572270983464846497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12709585526055955906257325 4766094572270983464846497)
                  ·
                    refine ⟨3574570929203237598634873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4766094572270983464846497 3574570929203237598634873)
                    ·
                      refine ⟨2680928196902428198976155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3574570929203237598634873 2680928196902428198976155)
                      ·
                        rfl

theorem cell23_5221089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 2, 3, 2, 2].length) (baseStart_5221089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5221089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5221089 prefixEnd_5221089 := by exact prefixLift 5221089
  have htrace : WordTrace (prefixWord ++ tailWord_5221089) baseStart_5221089 baseEnd_5221089 := by
    simpa [prefixWord, tailWord_5221089, baseEnd_5221089] using wordTrace_append hprefix tailTrace_5221089
  have hstable : (prefixWord ++ tailWord_5221089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5221089).length < 2 ^ (prefixWord ++ tailWord_5221089).sum := by decide
  have hdescent : baseEnd_5221089 < baseStart_5221089 := by decide
  rcases family_descends (prefixWord ++ tailWord_5221089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5221092 : List Nat := [2, 3, 1, 1, 1, 4, 1, 4, 1, 2, 3]
def baseStart_5221092 : Nat := 118140960795 + 5221092 * 2 ^ 59
def prefixEnd_5221092 : Nat := 4983230072969 + 3 ^ 40 * 5221092 * 2
def baseEnd_5221092 : Nat := 2680929737344391687238641

theorem tailTrace_5221092 : CollatzResearch.WordTrace tailWord_5221092 prefixEnd_5221092 2680929737344391687238641 := by
  unfold tailWord_5221092
  simp only [CollatzResearch.WordTrace]
  refine ⟨95214434800441425183760765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126952579733921900245014353 95214434800441425183760765)
  ·
    refine ⟨35705413050165534443910287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95214434800441425183760765 35705413050165534443910287)
    ·
      refine ⟨53558119575248301665865431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35705413050165534443910287 53558119575248301665865431)
      ·
        refine ⟨80337179362872452498798147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53558119575248301665865431 80337179362872452498798147)
        ·
          refine ⟨120505769044308678748197221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80337179362872452498798147 120505769044308678748197221)
          ·
            refine ⟨22594831695807877265286979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 120505769044308678748197221 22594831695807877265286979)
            ·
              refine ⟨33892247543711815897930469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22594831695807877265286979 33892247543711815897930469)
              ·
                refine ⟨6354796414445965480861963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33892247543711815897930469 6354796414445965480861963)
                ·
                  refine ⟨9532194621668948221292945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6354796414445965480861963 9532194621668948221292945)
                  ·
                    refine ⟨7149145966251711165969709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9532194621668948221292945 7149145966251711165969709)
                    ·
                      refine ⟨2680929737344391687238641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7149145966251711165969709 2680929737344391687238641)
                      ·
                        rfl

theorem cell23_5221092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 4, 1, 2, 3].length) (baseStart_5221092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5221092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5221092 prefixEnd_5221092 := by exact prefixLift 5221092
  have htrace : WordTrace (prefixWord ++ tailWord_5221092) baseStart_5221092 baseEnd_5221092 := by
    simpa [prefixWord, tailWord_5221092, baseEnd_5221092] using wordTrace_append hprefix tailTrace_5221092
  have hstable : (prefixWord ++ tailWord_5221092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5221092).length < 2 ^ (prefixWord ++ tailWord_5221092).sum := by decide
  have hdescent : baseEnd_5221092 < baseStart_5221092 := by decide
  rcases family_descends (prefixWord ++ tailWord_5221092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5221105 : List Nat := [1, 2, 2, 2, 2, 2, 2, 1, 3, 3, 3]
def baseStart_5221105 : Nat := 118140960795 + 5221105 * 2 ^ 59
def prefixEnd_5221105 : Nat := 4983230072969 + 3 ^ 40 * 5221105 * 2
def baseEnd_5221105 : Nat := 2680936412592900136376081

theorem tailTrace_5221105 : CollatzResearch.WordTrace tailWord_5221105 prefixEnd_5221105 2680936412592900136376081 := by
  unfold tailWord_5221105
  simp only [CollatzResearch.WordTrace]
  refine ⟨190429343749835753587744769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126952895833223835725163179 190429343749835753587744769)
  ·
    refine ⟨142822007812376815190808577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190429343749835753587744769 142822007812376815190808577)
    ·
      refine ⟨107116505859282611393106433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142822007812376815190808577 107116505859282611393106433)
      ·
        refine ⟨80337379394461958544829825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107116505859282611393106433 80337379394461958544829825)
        ·
          refine ⟨60253034545846468908622369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80337379394461958544829825 60253034545846468908622369)
          ·
            refine ⟨45189775909384851681466777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60253034545846468908622369 45189775909384851681466777)
            ·
              refine ⟨33892331932038638761100083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45189775909384851681466777 33892331932038638761100083)
              ·
                refine ⟨50838497898057958141650125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33892331932038638761100083 50838497898057958141650125)
                ·
                  refine ⟨19064436711771734303118797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50838497898057958141650125 19064436711771734303118797)
                  ·
                    refine ⟨7149163766914400363669549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19064436711771734303118797 7149163766914400363669549)
                    ·
                      refine ⟨2680936412592900136376081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7149163766914400363669549 2680936412592900136376081)
                      ·
                        rfl

theorem cell23_5221105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 3, 3, 3].length) (baseStart_5221105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5221105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5221105 prefixEnd_5221105 := by exact prefixLift 5221105
  have htrace : WordTrace (prefixWord ++ tailWord_5221105) baseStart_5221105 baseEnd_5221105 := by
    simpa [prefixWord, tailWord_5221105, baseEnd_5221105] using wordTrace_append hprefix tailTrace_5221105
  have hstable : (prefixWord ++ tailWord_5221105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5221105).length < 2 ^ (prefixWord ++ tailWord_5221105).sum := by decide
  have hdescent : baseEnd_5221105 < baseStart_5221105 := by decide
  rcases family_descends (prefixWord ++ tailWord_5221105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5221115 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 1, 9, 2]
def baseStart_5221115 : Nat := 118140960795 + 5221115 * 2 ^ 59
def prefixEnd_5221115 : Nat := 4983230072969 + 3 ^ 40 * 5221115 * 2
def baseEnd_5221115 : Nat := 2680941547399445097251035

theorem tailTrace_5221115 : CollatzResearch.WordTrace tailWord_5221115 prefixEnd_5221115 2680941547399445097251035 := by
  unfold tailWord_5221115
  simp only [CollatzResearch.WordTrace]
  refine ⟨190429708479799525295608799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126953138986533016863739199 190429708479799525295608799)
  ·
    refine ⟨285644562719699287943413199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190429708479799525295608799 285644562719699287943413199)
    ·
      refine ⟨428466844079548931915119799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285644562719699287943413199 428466844079548931915119799)
      ·
        refine ⟨642700266119323397872679699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 428466844079548931915119799 642700266119323397872679699)
        ·
          refine ⟨964050399178985096809019549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 642700266119323397872679699 964050399178985096809019549)
          ·
            refine ⟨361518899692119411303382331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 964050399178985096809019549 361518899692119411303382331)
            ·
              refine ⟨542278349538179116955073497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 361518899692119411303382331 542278349538179116955073497)
              ·
                refine ⟨406708762153634337716305123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 542278349538179116955073497 406708762153634337716305123)
                ·
                  refine ⟨610063143230451506574457685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 406708762153634337716305123 610063143230451506574457685)
                  ·
                    refine ⟨3574588729865926796334713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 610063143230451506574457685 3574588729865926796334713)
                    ·
                      refine ⟨2680941547399445097251035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3574588729865926796334713 2680941547399445097251035)
                      ·
                        rfl

theorem cell23_5221115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 9, 2].length) (baseStart_5221115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5221115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5221115 prefixEnd_5221115 := by exact prefixLift 5221115
  have htrace : WordTrace (prefixWord ++ tailWord_5221115) baseStart_5221115 baseEnd_5221115 := by
    simpa [prefixWord, tailWord_5221115, baseEnd_5221115] using wordTrace_append hprefix tailTrace_5221115
  have hstable : (prefixWord ++ tailWord_5221115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5221115).length < 2 ^ (prefixWord ++ tailWord_5221115).sum := by decide
  have hdescent : baseEnd_5221115 < baseStart_5221115 := by decide
  rcases family_descends (prefixWord ++ tailWord_5221115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5221132 : List Nat := [2, 2, 1, 2, 2, 1, 1, 4, 3, 3, 2]
def baseStart_5221132 : Nat := 118140960795 + 5221132 * 2 ^ 59
def prefixEnd_5221132 : Nat := 4983230072969 + 3 ^ 40 * 5221132 * 2
def baseEnd_5221132 : Nat := 2680950276570571530738457

theorem tailTrace_5221132 : CollatzResearch.WordTrace tailWord_5221132 prefixEnd_5221132 2680950276570571530738457 := by
  unfold tailWord_5221132
  simp only [CollatzResearch.WordTrace]
  refine ⟨95215164260368968599488825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126953552347158624799318433 95215164260368968599488825)
  ·
    refine ⟨71411373195276726449616619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95215164260368968599488825 71411373195276726449616619)
    ·
      refine ⟨107117059792915089674424929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71411373195276726449616619 107117059792915089674424929)
      ·
        refine ⟨80337794844686317255818697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107117059792915089674424929 80337794844686317255818697)
        ·
          refine ⟨60253346133514737941864023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80337794844686317255818697 60253346133514737941864023)
          ·
            refine ⟨90380019200272106912796035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60253346133514737941864023 90380019200272106912796035)
            ·
              refine ⟨135570028800408160369194053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90380019200272106912796035 135570028800408160369194053)
              ·
                refine ⟨25419380400076530069223885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 135570028800408160369194053 25419380400076530069223885)
                ·
                  refine ⟨9532267650028698775958957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25419380400076530069223885 9532267650028698775958957)
                  ·
                    refine ⟨3574600368760762040984609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9532267650028698775958957 3574600368760762040984609)
                    ·
                      refine ⟨2680950276570571530738457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3574600368760762040984609 2680950276570571530738457)
                      ·
                        rfl

theorem cell23_5221132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 3, 3, 2].length) (baseStart_5221132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5221132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5221132 prefixEnd_5221132 := by exact prefixLift 5221132
  have htrace : WordTrace (prefixWord ++ tailWord_5221132) baseStart_5221132 baseEnd_5221132 := by
    simpa [prefixWord, tailWord_5221132, baseEnd_5221132] using wordTrace_append hprefix tailTrace_5221132
  have hstable : (prefixWord ++ tailWord_5221132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5221132).length < 2 ^ (prefixWord ++ tailWord_5221132).sum := by decide
  have hdescent : baseEnd_5221132 < baseStart_5221132 := by decide
  rcases family_descends (prefixWord ++ tailWord_5221132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5221174 : List Nat := [5, 1, 2, 2, 3, 1, 2, 2, 1, 2, 2]
def baseStart_5221174 : Nat := 118140960795 + 5221174 * 2 ^ 59
def prefixEnd_5221174 : Nat := 4983230072969 + 3 ^ 40 * 5221174 * 2
def baseEnd_5221174 : Nat := 2680971842758060366413265

theorem tailTrace_5221174 : CollatzResearch.WordTrace tailWord_5221174 prefixEnd_5221174 2680971842758060366413265 := by
  unfold tailWord_5221174
  simp only [CollatzResearch.WordTrace]
  refine ⟨11901991274161611148250411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 126954573591057185581337717 11901991274161611148250411)
  ·
    refine ⟨17852986911242416722375617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11901991274161611148250411 17852986911242416722375617)
    ·
      refine ⟨13389740183431812541781713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17852986911242416722375617 13389740183431812541781713)
      ·
        refine ⟨10042305137573859406336285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13389740183431812541781713 10042305137573859406336285)
        ·
          refine ⟨3765864426590197277376107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10042305137573859406336285 3765864426590197277376107)
          ·
            refine ⟨5648796639885295916064161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3765864426590197277376107 5648796639885295916064161)
            ·
              refine ⟨4236597479913971937048121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5648796639885295916064161 4236597479913971937048121)
              ·
                refine ⟨3177448109935478952786091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4236597479913971937048121 3177448109935478952786091)
                ·
                  refine ⟨4766172164903218429179137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3177448109935478952786091 4766172164903218429179137)
                  ·
                    refine ⟨3574629123677413821884353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4766172164903218429179137 3574629123677413821884353)
                    ·
                      refine ⟨2680971842758060366413265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3574629123677413821884353 2680971842758060366413265)
                      ·
                        rfl

theorem cell23_5221174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_5221174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5221174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5221174 prefixEnd_5221174 := by exact prefixLift 5221174
  have htrace : WordTrace (prefixWord ++ tailWord_5221174) baseStart_5221174 baseEnd_5221174 := by
    simpa [prefixWord, tailWord_5221174, baseEnd_5221174] using wordTrace_append hprefix tailTrace_5221174
  have hstable : (prefixWord ++ tailWord_5221174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5221174).length < 2 ^ (prefixWord ++ tailWord_5221174).sum := by decide
  have hdescent : baseEnd_5221174 < baseStart_5221174 := by decide
  rcases family_descends (prefixWord ++ tailWord_5221174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5221175 : List Nat := [1, 1, 3, 1, 2, 1, 4, 2, 2, 2, 4]
def baseStart_5221175 : Nat := 118140960795 + 5221175 * 2 ^ 59
def prefixEnd_5221175 : Nat := 4983230072969 + 3 ^ 40 * 5221175 * 2
def baseEnd_5221175 : Nat := 2680972356238714862500759

theorem tailTrace_5221175 : CollatzResearch.WordTrace tailWord_5221175 prefixEnd_5221175 2680972356238714862500759 := by
  unfold tailWord_5221175
  simp only [CollatzResearch.WordTrace]
  refine ⟨190431896859582155542792979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126954597906388103695195319 190431896859582155542792979)
  ·
    refine ⟨285647845289373233314189469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190431896859582155542792979 285647845289373233314189469)
    ·
      refine ⟨107117941983514962492821051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 285647845289373233314189469 107117941983514962492821051)
      ·
        refine ⟨160676912975272443739231577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107117941983514962492821051 160676912975272443739231577)
        ·
          refine ⟨120507684731454332804423683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160676912975272443739231577 120507684731454332804423683)
          ·
            refine ⟨180761527097181499206635525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120507684731454332804423683 180761527097181499206635525)
            ·
              refine ⟨33892786330721531101244161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 180761527097181499206635525 33892786330721531101244161)
              ·
                refine ⟨25419589748041148325933121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33892786330721531101244161 25419589748041148325933121)
                ·
                  refine ⟨19064692311030861244449841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25419589748041148325933121 19064692311030861244449841)
                  ·
                    refine ⟨14298519233273145933337381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19064692311030861244449841 14298519233273145933337381)
                    ·
                      refine ⟨2680972356238714862500759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14298519233273145933337381 2680972356238714862500759)
                      ·
                        rfl

theorem cell23_5221175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 2, 2, 4].length) (baseStart_5221175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5221175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5221175 prefixEnd_5221175 := by exact prefixLift 5221175
  have htrace : WordTrace (prefixWord ++ tailWord_5221175) baseStart_5221175 baseEnd_5221175 := by
    simpa [prefixWord, tailWord_5221175, baseEnd_5221175] using wordTrace_append hprefix tailTrace_5221175
  have hstable : (prefixWord ++ tailWord_5221175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5221175).length < 2 ^ (prefixWord ++ tailWord_5221175).sum := by decide
  have hdescent : baseEnd_5221175 < baseStart_5221175 := by decide
  rcases family_descends (prefixWord ++ tailWord_5221175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5221196 : List Nat := [2, 2, 1, 3, 3, 1, 2, 3, 2, 2, 2]
def baseStart_5221196 : Nat := 118140960795 + 5221196 * 2 ^ 59
def prefixEnd_5221196 : Nat := 4983230072969 + 3 ^ 40 * 5221196 * 2
def baseEnd_5221196 : Nat := 2680983139332459280338163

theorem tailTrace_5221196 : CollatzResearch.WordTrace tailWord_5221196 prefixEnd_5221196 2680983139332459280338163 := by
  unfold tailWord_5221196
  simp only [CollatzResearch.WordTrace]
  refine ⟨95216331396253038064653721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126955108528337384086204961 95216331396253038064653721)
  ·
    refine ⟨71412248547189778548490291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95216331396253038064653721 71412248547189778548490291)
    ·
      refine ⟨107118372820784667822735437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71412248547189778548490291 107118372820784667822735437)
      ·
        refine ⟨40169389807794250433525789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107118372820784667822735437 40169389807794250433525789)
        ·
          refine ⟨15063521177922843912572171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40169389807794250433525789 15063521177922843912572171)
          ·
            refine ⟨22595281766884265868858257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15063521177922843912572171 22595281766884265868858257)
            ·
              refine ⟨16946461325163199401643693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22595281766884265868858257 16946461325163199401643693)
              ·
                refine ⟨6354922996936199775616385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16946461325163199401643693 6354922996936199775616385)
                ·
                  refine ⟨4766192247702149831712289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6354922996936199775616385 4766192247702149831712289)
                  ·
                    refine ⟨3574644185776612373784217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4766192247702149831712289 3574644185776612373784217)
                    ·
                      refine ⟨2680983139332459280338163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3574644185776612373784217 2680983139332459280338163)
                      ·
                        rfl

theorem cell23_5221196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 3, 2, 2, 2].length) (baseStart_5221196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5221196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5221196 prefixEnd_5221196 := by exact prefixLift 5221196
  have htrace : WordTrace (prefixWord ++ tailWord_5221196) baseStart_5221196 baseEnd_5221196 := by
    simpa [prefixWord, tailWord_5221196, baseEnd_5221196] using wordTrace_append hprefix tailTrace_5221196
  have hstable : (prefixWord ++ tailWord_5221196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5221196).length < 2 ^ (prefixWord ++ tailWord_5221196).sum := by decide
  have hdescent : baseEnd_5221196 < baseStart_5221196 := by decide
  rcases family_descends (prefixWord ++ tailWord_5221196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5221215 : List Nat := [1, 1, 2, 3, 1, 3, 3, 1, 1, 7]
def baseStart_5221215 : Nat := 118140960795 + 5221215 * 2 ^ 59
def prefixEnd_5221215 : Nat := 4983230072969 + 3 ^ 40 * 5221215 * 2
def baseEnd_5221215 : Nat := 893664298488298235333525

theorem tailTrace_5221215 : CollatzResearch.WordTrace tailWord_5221215 prefixEnd_5221215 893664298488298235333525 := by
  unfold tailWord_5221215
  simp only [CollatzResearch.WordTrace]
  refine ⟨190433355779437242374249099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126955570519624828249499399 190433355779437242374249099)
  ·
    refine ⟨285650033669155863561373649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190433355779437242374249099 285650033669155863561373649)
    ·
      refine ⟨214237525251866897671030237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 285650033669155863561373649 214237525251866897671030237)
      ·
        refine ⟨80339071969450086626636339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 214237525251866897671030237 80339071969450086626636339)
        ·
          refine ⟨120508607954175129939954509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80339071969450086626636339 120508607954175129939954509)
          ·
            refine ⟨45190727982815673727482941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120508607954175129939954509 45190727982815673727482941)
            ·
              refine ⟨16946522993555877647806103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45190727982815673727482941 16946522993555877647806103)
              ·
                refine ⟨25419784490333816471709155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16946522993555877647806103 25419784490333816471709155)
                ·
                  refine ⟨38129676735500724707563733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25419784490333816471709155 38129676735500724707563733)
                  ·
                    refine ⟨893664298488298235333525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38129676735500724707563733 893664298488298235333525)
                    ·
                      rfl

theorem cell23_5221215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 7].length) (baseStart_5221215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5221215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5221215 prefixEnd_5221215 := by exact prefixLift 5221215
  have htrace : WordTrace (prefixWord ++ tailWord_5221215) baseStart_5221215 baseEnd_5221215 := by
    simpa [prefixWord, tailWord_5221215, baseEnd_5221215] using wordTrace_append hprefix tailTrace_5221215
  have hstable : (prefixWord ++ tailWord_5221215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5221215).length < 2 ^ (prefixWord ++ tailWord_5221215).sum := by decide
  have hdescent : baseEnd_5221215 < baseStart_5221215 := by decide
  rcases family_descends (prefixWord ++ tailWord_5221215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5221219 : List Nat := [1, 1, 1, 5, 3, 2, 2, 3, 5]
def baseStart_5221219 : Nat := 118140960795 + 5221219 * 2 ^ 59
def prefixEnd_5221219 : Nat := 4983230072969 + 3 ^ 40 * 5221219 * 2
def baseEnd_5221219 : Nat := 297888327709723632261173

theorem tailTrace_5221219 : CollatzResearch.WordTrace tailWord_5221219 prefixEnd_5221219 297888327709723632261173 := by
  unfold tailWord_5221219
  simp only [CollatzResearch.WordTrace]
  refine ⟨190433501671422751057394711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126955667780948500704929807 190433501671422751057394711)
  ·
    refine ⟨285650252507134126586092067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190433501671422751057394711 285650252507134126586092067)
    ·
      refine ⟨428475378760701189879138101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285650252507134126586092067 428475378760701189879138101)
      ·
        refine ⟨40169566758815736551169197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 428475378760701189879138101 40169566758815736551169197)
        ·
          refine ⟨15063587534555901206688449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40169566758815736551169197 15063587534555901206688449)
          ·
            refine ⟨11297690650916925905016337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15063587534555901206688449 11297690650916925905016337)
            ·
              refine ⟨8473267988187694428762253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11297690650916925905016337 8473267988187694428762253)
              ·
                refine ⟨3177475495570385410785845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8473267988187694428762253 3177475495570385410785845)
                ·
                  refine ⟨297888327709723632261173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3177475495570385410785845 297888327709723632261173)
                  ·
                    rfl

theorem cell23_5221219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 3, 5].length) (baseStart_5221219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5221219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5221219 prefixEnd_5221219 := by exact prefixLift 5221219
  have htrace : WordTrace (prefixWord ++ tailWord_5221219) baseStart_5221219 baseEnd_5221219 := by
    simpa [prefixWord, tailWord_5221219, baseEnd_5221219] using wordTrace_append hprefix tailTrace_5221219
  have hstable : (prefixWord ++ tailWord_5221219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5221219).length < 2 ^ (prefixWord ++ tailWord_5221219).sum := by decide
  have hdescent : baseEnd_5221219 < baseStart_5221219 := by decide
  rcases family_descends (prefixWord ++ tailWord_5221219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5221230 : List Nat := [4, 1, 2, 3, 2, 2, 1, 2, 2, 2, 2]
def baseStart_5221230 : Nat := 118140960795 + 5221230 * 2 ^ 59
def prefixEnd_5221230 : Nat := 4983230072969 + 3 ^ 40 * 5221230 * 2
def baseEnd_5221230 : Nat := 2681000597674712147313007

theorem tailTrace_5221230 : CollatzResearch.WordTrace tailWord_5221230 prefixEnd_5221230 2681000597674712147313007 := by
  unfold tailWord_5221230
  simp only [CollatzResearch.WordTrace]
  refine ⟨23804237859297862492005643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126955935249588599957363429 23804237859297862492005643)
  ·
    refine ⟨35706356788946793738008465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23804237859297862492005643 35706356788946793738008465)
    ·
      refine ⟨26779767591710095303506349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35706356788946793738008465 26779767591710095303506349)
      ·
        refine ⟨10042412846891285738814881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26779767591710095303506349 10042412846891285738814881)
        ·
          refine ⟨7531809635168464304111161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10042412846891285738814881 7531809635168464304111161)
          ·
            refine ⟨5648857226376348228083371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7531809635168464304111161 5648857226376348228083371)
            ·
              refine ⟨8473285839564522342125057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5648857226376348228083371 8473285839564522342125057)
              ·
                refine ⟨6354964379673391756593793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8473285839564522342125057 6354964379673391756593793)
                ·
                  refine ⟨4766223284755043817445345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6354964379673391756593793 4766223284755043817445345)
                  ·
                    refine ⟨3574667463566282863084009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4766223284755043817445345 3574667463566282863084009)
                    ·
                      refine ⟨2681000597674712147313007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3574667463566282863084009 2681000597674712147313007)
                      ·
                        rfl

theorem cell23_5221230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_5221230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5221230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5221230 prefixEnd_5221230 := by exact prefixLift 5221230
  have htrace : WordTrace (prefixWord ++ tailWord_5221230) baseStart_5221230 baseEnd_5221230 := by
    simpa [prefixWord, tailWord_5221230, baseEnd_5221230] using wordTrace_append hprefix tailTrace_5221230
  have hstable : (prefixWord ++ tailWord_5221230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5221230).length < 2 ^ (prefixWord ++ tailWord_5221230).sum := by decide
  have hdescent : baseEnd_5221230 < baseStart_5221230 := by decide
  rcases family_descends (prefixWord ++ tailWord_5221230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5221265 : List Nat := [1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 4]
def baseStart_5221265 : Nat := 118140960795 + 5221265 * 2 ^ 59
def prefixEnd_5221265 : Nat := 4983230072969 + 3 ^ 40 * 5221265 * 2
def baseEnd_5221265 : Nat := 2681018569497619510375345

theorem tailTrace_5221265 : CollatzResearch.WordTrace tailWord_5221265 prefixEnd_5221265 2681018569497619510375345 := by
  unfold tailWord_5221265
  simp only [CollatzResearch.WordTrace]
  refine ⟨190435179429256100913569249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126956786286170733942379499 190435179429256100913569249)
  ·
    refine ⟨142826384571942075685176937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190435179429256100913569249 142826384571942075685176937)
    ·
      refine ⟨107119788428956556763882703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142826384571942075685176937 107119788428956556763882703)
      ·
        refine ⟨160679682643434835145824055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107119788428956556763882703 160679682643434835145824055)
        ·
          refine ⟨241019523965152252718736083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160679682643434835145824055 241019523965152252718736083)
          ·
            refine ⟨361529285947728379078104125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241019523965152252718736083 361529285947728379078104125)
            ·
              refine ⟨135573482230398142154289047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 361529285947728379078104125 135573482230398142154289047)
              ·
                refine ⟨203360223345597213231433571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135573482230398142154289047 203360223345597213231433571)
                ·
                  refine ⟨305040335018395819847150357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 203360223345597213231433571 305040335018395819847150357)
                  ·
                    refine ⟨14298765703987304055335173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 305040335018395819847150357 14298765703987304055335173)
                    ·
                      refine ⟨2681018569497619510375345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14298765703987304055335173 2681018569497619510375345)
                      ·
                        rfl

theorem cell23_5221265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 4].length) (baseStart_5221265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5221265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5221265 prefixEnd_5221265 := by exact prefixLift 5221265
  have htrace : WordTrace (prefixWord ++ tailWord_5221265) baseStart_5221265 baseEnd_5221265 := by
    simpa [prefixWord, tailWord_5221265, baseEnd_5221265] using wordTrace_append hprefix tailTrace_5221265
  have hstable : (prefixWord ++ tailWord_5221265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5221265).length < 2 ^ (prefixWord ++ tailWord_5221265).sum := by decide
  have hdescent : baseEnd_5221265 < baseStart_5221265 := by decide
  rcases family_descends (prefixWord ++ tailWord_5221265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5221270 : List Nat := [5, 3, 1, 1, 1, 3, 1, 3, 5]
def baseStart_5221270 : Nat := 118140960795 + 5221270 * 2 ^ 59
def prefixEnd_5221270 : Nat := 4983230072969 + 3 ^ 40 * 5221270 * 2
def baseEnd_5221270 : Nat := 297891237433432443423647

theorem tailTrace_5221270 : CollatzResearch.WordTrace tailWord_5221270 prefixEnd_5221270 297891237433432443423647 := by
  unfold tailWord_5221270
  simp only [CollatzResearch.WordTrace]
  refine ⟨11902210112139874172968829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 126956907862825324511667509 11902210112139874172968829)
  ·
    refine ⟨4463328792052452814863311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11902210112139874172968829 4463328792052452814863311)
    ·
      refine ⟨6694993188078679222294967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4463328792052452814863311 6694993188078679222294967)
      ·
        refine ⟨10042489782118018833442451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6694993188078679222294967 10042489782118018833442451)
        ·
          refine ⟨15063734673177028250163677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10042489782118018833442451 15063734673177028250163677)
          ·
            refine ⟨5648900502441385593811379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15063734673177028250163677 5648900502441385593811379)
            ·
              refine ⟨8473350753662078390717069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5648900502441385593811379 8473350753662078390717069)
              ·
                refine ⟨3177506532623279396518901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8473350753662078390717069 3177506532623279396518901)
                ·
                  refine ⟨297891237433432443423647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3177506532623279396518901 297891237433432443423647)
                  ·
                    rfl

theorem cell23_5221270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_5221270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5221270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5221270 prefixEnd_5221270 := by exact prefixLift 5221270
  have htrace : WordTrace (prefixWord ++ tailWord_5221270) baseStart_5221270 baseEnd_5221270 := by
    simpa [prefixWord, tailWord_5221270, baseEnd_5221270] using wordTrace_append hprefix tailTrace_5221270
  have hstable : (prefixWord ++ tailWord_5221270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5221270).length < 2 ^ (prefixWord ++ tailWord_5221270).sum := by decide
  have hdescent : baseEnd_5221270 < baseStart_5221270 := by decide
  rcases family_descends (prefixWord ++ tailWord_5221270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5221295 : List Nat := [1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 6]
def baseStart_5221295 : Nat := 118140960795 + 5221295 * 2 ^ 59
def prefixEnd_5221295 : Nat := 4983230072969 + 3 ^ 40 * 5221295 * 2
def baseEnd_5221295 : Nat := 2681033973917254393000207

theorem tailTrace_5221295 : CollatzResearch.WordTrace tailWord_5221295 prefixEnd_5221295 2681033973917254393000207 := by
  unfold tailWord_5221295
  simp only [CollatzResearch.WordTrace]
  refine ⟨190436273619147416037161339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126957515746098277358107559 190436273619147416037161339)
  ·
    refine ⟨285654410428721124055742009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190436273619147416037161339 285654410428721124055742009)
    ·
      refine ⟨214240807821540843041806507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 285654410428721124055742009 214240807821540843041806507)
      ·
        refine ⟨321361211732311264562709761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214240807821540843041806507 321361211732311264562709761)
        ·
          refine ⟨241020908799233448422032321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 321361211732311264562709761 241020908799233448422032321)
          ·
            refine ⟨180765681599425086316524241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 241020908799233448422032321 180765681599425086316524241)
            ·
              refine ⟨135574261199568814737393181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 180765681599425086316524241 135574261199568814737393181)
              ·
                refine ⟨50840347949838305526522443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 135574261199568814737393181 50840347949838305526522443)
                ·
                  refine ⟨76260521924757458289783665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50840347949838305526522443 76260521924757458289783665)
                  ·
                    refine ⟨57195391443568093717337749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 76260521924757458289783665 57195391443568093717337749)
                    ·
                      refine ⟨2681033973917254393000207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57195391443568093717337749 2681033973917254393000207)
                      ·
                        rfl

theorem cell23_5221295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 6].length) (baseStart_5221295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5221295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5221295 prefixEnd_5221295 := by exact prefixLift 5221295
  have htrace : WordTrace (prefixWord ++ tailWord_5221295) baseStart_5221295 baseEnd_5221295 := by
    simpa [prefixWord, tailWord_5221295, baseEnd_5221295] using wordTrace_append hprefix tailTrace_5221295
  have hstable : (prefixWord ++ tailWord_5221295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5221295).length < 2 ^ (prefixWord ++ tailWord_5221295).sum := by decide
  have hdescent : baseEnd_5221295 < baseStart_5221295 := by decide
  rcases family_descends (prefixWord ++ tailWord_5221295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5221309 : List Nat := [1, 4, 1, 2, 4, 1, 1, 3, 6]
def baseStart_5221309 : Nat := 118140960795 + 5221309 * 2 ^ 59
def prefixEnd_5221309 : Nat := 4983230072969 + 3 ^ 40 * 5221309 * 2
def baseEnd_5221309 : Nat := 297893462516268593136127

theorem tailTrace_5221309 : CollatzResearch.WordTrace tailWord_5221309 prefixEnd_5221309 297893462516268593136127 := by
  unfold tailWord_5221309
  simp only [CollatzResearch.WordTrace]
  refine ⟨190436784241096696428170981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126957856160731130952113987 190436784241096696428170981)
  ·
    refine ⟨35706897045205630580282059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 190436784241096696428170981 35706897045205630580282059)
    ·
      refine ⟨53560345567808445870423089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35706897045205630580282059 53560345567808445870423089)
      ·
        refine ⟨40170259175856334402817317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53560345567808445870423089 40170259175856334402817317)
        ·
          refine ⟨7531923595473062700528247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40170259175856334402817317 7531923595473062700528247)
          ·
            refine ⟨11297885393209594050792371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7531923595473062700528247 11297885393209594050792371)
            ·
              refine ⟨16946828089814391076188557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11297885393209594050792371 16946828089814391076188557)
              ·
                refine ⟨6355060533680396653570709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16946828089814391076188557 6355060533680396653570709)
                ·
                  refine ⟨297893462516268593136127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6355060533680396653570709 297893462516268593136127)
                  ·
                    rfl

theorem cell23_5221309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 3, 6].length) (baseStart_5221309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5221309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5221309 prefixEnd_5221309 := by exact prefixLift 5221309
  have htrace : WordTrace (prefixWord ++ tailWord_5221309) baseStart_5221309 baseEnd_5221309 := by
    simpa [prefixWord, tailWord_5221309, baseEnd_5221309] using wordTrace_append hprefix tailTrace_5221309
  have hstable : (prefixWord ++ tailWord_5221309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5221309).length < 2 ^ (prefixWord ++ tailWord_5221309).sum := by decide
  have hdescent : baseEnd_5221309 < baseStart_5221309 := by decide
  rcases family_descends (prefixWord ++ tailWord_5221309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5221315 : List Nat := [1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 7]
def baseStart_5221315 : Nat := 118140960795 + 5221315 * 2 ^ 59
def prefixEnd_5221315 : Nat := 4983230072969 + 3 ^ 40 * 5221315 * 2
def baseEnd_5221315 : Nat := 2681044243530344314750115

theorem tailTrace_5221315 : CollatzResearch.WordTrace tailWord_5221315 prefixEnd_5221315 2681044243530344314750115 := by
  unfold tailWord_5221315
  simp only [CollatzResearch.WordTrace]
  refine ⟨190437003079074959452889399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126958002052716639635259599 190437003079074959452889399)
  ·
    refine ⟨285655504618612439179334099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190437003079074959452889399 285655504618612439179334099)
    ·
      refine ⟨428483256927918658769001149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285655504618612439179334099 428483256927918658769001149)
      ·
        refine ⟨160681221347969497038375431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 428483256927918658769001149 160681221347969497038375431)
        ·
          refine ⟨241021832021954245557563147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160681221347969497038375431 241021832021954245557563147)
          ·
            refine ⟨361532748032931368336344721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241021832021954245557563147 361532748032931368336344721)
            ·
              refine ⟨271149561024698526252258541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 361532748032931368336344721 271149561024698526252258541)
              ·
                refine ⟨101681085384261947344596953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 271149561024698526252258541 101681085384261947344596953)
                ·
                  refine ⟨76260814038196460508447715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101681085384261947344596953 76260814038196460508447715)
                  ·
                    refine ⟨114391221057294690762671573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 76260814038196460508447715 114391221057294690762671573)
                    ·
                      refine ⟨2681044243530344314750115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 114391221057294690762671573 2681044243530344314750115)
                      ·
                        rfl

theorem cell23_5221315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 7].length) (baseStart_5221315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5221315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5221315 prefixEnd_5221315 := by exact prefixLift 5221315
  have htrace : WordTrace (prefixWord ++ tailWord_5221315) baseStart_5221315 baseEnd_5221315 := by
    simpa [prefixWord, tailWord_5221315, baseEnd_5221315] using wordTrace_append hprefix tailTrace_5221315
  have hstable : (prefixWord ++ tailWord_5221315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5221315).length < 2 ^ (prefixWord ++ tailWord_5221315).sum := by decide
  have hdescent : baseEnd_5221315 < baseStart_5221315 := by decide
  rcases family_descends (prefixWord ++ tailWord_5221315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5221319 : List Nat := [1, 1, 4, 1, 1, 2, 2, 4, 3, 1, 3]
def baseStart_5221319 : Nat := 118140960795 + 5221319 * 2 ^ 59
def prefixEnd_5221319 : Nat := 4983230072969 + 3 ^ 40 * 5221319 * 2
def baseEnd_5221319 : Nat := 2681046297452962299100097

theorem tailTrace_5221319 : CollatzResearch.WordTrace tailWord_5221319 prefixEnd_5221319 2681046297452962299100097 := by
  unfold tailWord_5221319
  simp only [CollatzResearch.WordTrace]
  refine ⟨190437148971060468136035011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126958099314040312090690007 190437148971060468136035011)
  ·
    refine ⟨285655723456590702204052517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190437148971060468136035011 285655723456590702204052517)
    ·
      refine ⟨53560448148110756663259847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 285655723456590702204052517 53560448148110756663259847)
      ·
        refine ⟨80340672222166134994889771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53560448148110756663259847 80340672222166134994889771)
        ·
          refine ⟨120511008333249202492334657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80340672222166134994889771 120511008333249202492334657)
          ·
            refine ⟨90383256249936901869250993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120511008333249202492334657 90383256249936901869250993)
            ·
              refine ⟨67787442187452676401938245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90383256249936901869250993 67787442187452676401938245)
              ·
                refine ⟨12710145410147376825363421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67787442187452676401938245 12710145410147376825363421)
                ·
                  refine ⟨4766304528805266309511283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12710145410147376825363421 4766304528805266309511283)
                  ·
                    refine ⟨7149456793207899464266925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4766304528805266309511283 7149456793207899464266925)
                    ·
                      refine ⟨2681046297452962299100097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7149456793207899464266925 2681046297452962299100097)
                      ·
                        rfl

theorem cell23_5221319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 4, 3, 1, 3].length) (baseStart_5221319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5221319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5221319 prefixEnd_5221319 := by exact prefixLift 5221319
  have htrace : WordTrace (prefixWord ++ tailWord_5221319) baseStart_5221319 baseEnd_5221319 := by
    simpa [prefixWord, tailWord_5221319, baseEnd_5221319] using wordTrace_append hprefix tailTrace_5221319
  have hstable : (prefixWord ++ tailWord_5221319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5221319).length < 2 ^ (prefixWord ++ tailWord_5221319).sum := by decide
  have hdescent : baseEnd_5221319 < baseStart_5221319 := by decide
  rcases family_descends (prefixWord ++ tailWord_5221319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5221369 : List Nat := [1, 2, 1, 3, 1, 3, 1, 5, 2, 4]
def baseStart_5221369 : Nat := 118140960795 + 5221369 * 2 ^ 59
def prefixEnd_5221369 : Nat := 4983230072969 + 3 ^ 40 * 5221369 * 2
def baseEnd_5221369 : Nat := 893690657161895701158289

theorem tailTrace_5221369 : CollatzResearch.WordTrace tailWord_5221369 prefixEnd_5221369 893690657161895701158289 := by
  unfold tailWord_5221369
  simp only [CollatzResearch.WordTrace]
  refine ⟨190438972620879326675355161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126959315080586217783570107 190438972620879326675355161)
  ·
    refine ⟨142829229465659495006516371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190438972620879326675355161 142829229465659495006516371)
    ·
      refine ⟨214243844198489242509774557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142829229465659495006516371 214243844198489242509774557)
      ·
        refine ⟨80341441574433465941165459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 214243844198489242509774557 80341441574433465941165459)
        ·
          refine ⟨120512162361650198911748189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80341441574433465941165459 120512162361650198911748189)
          ·
            refine ⟨45192060885618824591905571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120512162361650198911748189 45192060885618824591905571)
            ·
              refine ⟨67788091328428236887858357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45192060885618824591905571 67788091328428236887858357)
              ·
                refine ⟨6355133562040147208236721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67788091328428236887858357 6355133562040147208236721)
                ·
                  refine ⟨4766350171530110406177541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6355133562040147208236721 4766350171530110406177541)
                  ·
                    refine ⟨893690657161895701158289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4766350171530110406177541 893690657161895701158289)
                    ·
                      rfl

theorem cell23_5221369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 5, 2, 4].length) (baseStart_5221369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5221369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5221369 prefixEnd_5221369 := by exact prefixLift 5221369
  have htrace : WordTrace (prefixWord ++ tailWord_5221369) baseStart_5221369 baseEnd_5221369 := by
    simpa [prefixWord, tailWord_5221369, baseEnd_5221369] using wordTrace_append hprefix tailTrace_5221369
  have hstable : (prefixWord ++ tailWord_5221369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5221369).length < 2 ^ (prefixWord ++ tailWord_5221369).sum := by decide
  have hdescent : baseEnd_5221369 < baseStart_5221369 := by decide
  rcases family_descends (prefixWord ++ tailWord_5221369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5221410 : List Nat := [3, 3, 1, 1, 1, 3, 2, 4, 1, 2, 2]
def baseStart_5221410 : Nat := 118140960795 + 5221410 * 2 ^ 59
def prefixEnd_5221410 : Nat := 4983230072969 + 3 ^ 40 * 5221410 * 2
def baseEnd_5221410 : Nat := 2681093024192521443062179

theorem tailTrace_5221410 : CollatzResearch.WordTrace tailWord_5221410 prefixEnd_5221410 2681093024192521443062179 := by
  unfold tailWord_5221410
  simp only [CollatzResearch.WordTrace]
  refine ⟨47610117003432697669399421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126960312009153860451731789 47610117003432697669399421)
  ·
    refine ⟨17853793876287261626024783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47610117003432697669399421 17853793876287261626024783)
    ·
      refine ⟨26780690814430892439037175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17853793876287261626024783 26780690814430892439037175)
      ·
        refine ⟨40171036221646338658555763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26780690814430892439037175 40171036221646338658555763)
        ·
          refine ⟨60256554332469507987833645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40171036221646338658555763 60256554332469507987833645)
          ·
            refine ⟨22596207874676065495437617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60256554332469507987833645 22596207874676065495437617)
            ·
              refine ⟨16947155906007049121578213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22596207874676065495437617 16947155906007049121578213)
              ·
                refine ⟨3177591732376321710295915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16947155906007049121578213 3177591732376321710295915)
                ·
                  refine ⟨4766387598564482565443873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3177591732376321710295915 4766387598564482565443873)
                  ·
                    refine ⟨3574790698923361924082905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4766387598564482565443873 3574790698923361924082905)
                    ·
                      refine ⟨2681093024192521443062179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3574790698923361924082905 2681093024192521443062179)
                      ·
                        rfl

theorem cell23_5221410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 4, 1, 2, 2].length) (baseStart_5221410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5221410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5221410 prefixEnd_5221410 := by exact prefixLift 5221410
  have htrace : WordTrace (prefixWord ++ tailWord_5221410) baseStart_5221410 baseEnd_5221410 := by
    simpa [prefixWord, tailWord_5221410, baseEnd_5221410] using wordTrace_append hprefix tailTrace_5221410
  have hstable : (prefixWord ++ tailWord_5221410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5221410).length < 2 ^ (prefixWord ++ tailWord_5221410).sum := by decide
  have hdescent : baseEnd_5221410 < baseStart_5221410 := by decide
  rcases family_descends (prefixWord ++ tailWord_5221410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5221539 : List Nat := [1, 1, 1, 4, 1, 1, 1, 4, 4, 1, 4]
def baseStart_5221539 : Nat := 118140960795 + 5221539 * 2 ^ 59
def prefixEnd_5221539 : Nat := 4983230072969 + 3 ^ 40 * 5221539 * 2
def baseEnd_5221539 : Nat := 2681159263196951438349085

theorem tailTrace_5221539 : CollatzResearch.WordTrace tailWord_5221539 prefixEnd_5221539 2681159263196951438349085 := by
  unfold tailWord_5221539
  simp only [CollatzResearch.WordTrace]
  refine ⟨190445173030263445709043671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126963448686842297139362447 190445173030263445709043671)
  ·
    refine ⟨285667759545395168563565507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190445173030263445709043671 285667759545395168563565507)
    ·
      refine ⟨428501639318092752845348261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285667759545395168563565507 428501639318092752845348261)
      ·
        refine ⟨80344057372142391158502799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 428501639318092752845348261 80344057372142391158502799)
        ·
          refine ⟨120516086058213586737754199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80344057372142391158502799 120516086058213586737754199)
          ·
            refine ⟨180774129087320380106631299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120516086058213586737754199 180774129087320380106631299)
            ·
              refine ⟨271161193630980570159946949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180774129087320380106631299 271161193630980570159946949)
              ·
                refine ⟨50842723805808856904990053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 271161193630980570159946949 50842723805808856904990053)
                ·
                  refine ⟨9533010713589160669685635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50842723805808856904990053 9533010713589160669685635)
                  ·
                    refine ⟨14299516070383741004528453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9533010713589160669685635 14299516070383741004528453)
                    ·
                      refine ⟨2681159263196951438349085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14299516070383741004528453 2681159263196951438349085)
                      ·
                        rfl

theorem cell23_5221539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 4, 1, 4].length) (baseStart_5221539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5221539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5221539 prefixEnd_5221539 := by exact prefixLift 5221539
  have htrace : WordTrace (prefixWord ++ tailWord_5221539) baseStart_5221539 baseEnd_5221539 := by
    simpa [prefixWord, tailWord_5221539, baseEnd_5221539] using wordTrace_append hprefix tailTrace_5221539
  have hstable : (prefixWord ++ tailWord_5221539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5221539).length < 2 ^ (prefixWord ++ tailWord_5221539).sum := by decide
  have hdescent : baseEnd_5221539 < baseStart_5221539 := by decide
  rcases family_descends (prefixWord ++ tailWord_5221539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5221553 : List Nat := [1, 2, 2, 5, 1, 3, 1, 1, 2, 5]
def baseStart_5221553 : Nat := 118140960795 + 5221553 * 2 ^ 59
def prefixEnd_5221553 : Nat := 4983230072969 + 3 ^ 40 * 5221553 * 2
def baseEnd_5221553 : Nat := 893722150642038127858007

theorem tailTrace_5221553 : CollatzResearch.WordTrace tailWord_5221553 prefixEnd_5221553 893722150642038127858007 := by
  unfold tailWord_5221553
  simp only [CollatzResearch.WordTrace]
  refine ⟨190445683652212726100053313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126963789101475150733368875 190445683652212726100053313)
  ·
    refine ⟨142834262739159544575039985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190445683652212726100053313 142834262739159544575039985)
    ·
      refine ⟨107125697054369658431279989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142834262739159544575039985 107125697054369658431279989)
      ·
        refine ⟨10043034098847155477932499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 107125697054369658431279989 10043034098847155477932499)
        ·
          refine ⟨15064551148270733216898749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10043034098847155477932499 15064551148270733216898749)
          ·
            refine ⟨5649206680601524956337031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15064551148270733216898749 5649206680601524956337031)
            ·
              refine ⟨8473810020902287434505547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5649206680601524956337031 8473810020902287434505547)
              ·
                refine ⟨12710715031353431151758321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8473810020902287434505547 12710715031353431151758321)
                ·
                  refine ⟨9533036273515073363818741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12710715031353431151758321 9533036273515073363818741)
                  ·
                    refine ⟨893722150642038127858007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9533036273515073363818741 893722150642038127858007)
                    ·
                      rfl

theorem cell23_5221553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 1, 2, 5].length) (baseStart_5221553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5221553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5221553 prefixEnd_5221553 := by exact prefixLift 5221553
  have htrace : WordTrace (prefixWord ++ tailWord_5221553) baseStart_5221553 baseEnd_5221553 := by
    simpa [prefixWord, tailWord_5221553, baseEnd_5221553] using wordTrace_append hprefix tailTrace_5221553
  have hstable : (prefixWord ++ tailWord_5221553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5221553).length < 2 ^ (prefixWord ++ tailWord_5221553).sum := by decide
  have hdescent : baseEnd_5221553 < baseStart_5221553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5221553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5221576 : List Nat := [2, 1, 3, 1, 2, 1, 2, 4, 2, 2, 3]
def baseStart_5221576 : Nat := 118140960795 + 5221576 * 2 ^ 59
def prefixEnd_5221576 : Nat := 4983230072969 + 3 ^ 40 * 5221576 * 2
def baseEnd_5221576 : Nat := 2681178261981167793586415

theorem tailTrace_5221576 : CollatzResearch.WordTrace tailWord_5221576 prefixEnd_5221576 2681178261981167793586415 := by
  unfold tailWord_5221576
  simp only [CollatzResearch.WordTrace]
  refine ⟨95223261265564700514070291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126964348354086267352093721 95223261265564700514070291)
  ·
    refine ⟨142834891898347050771105437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95223261265564700514070291 142834891898347050771105437)
    ·
      refine ⟨53563084461880144039164539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142834891898347050771105437 53563084461880144039164539)
      ·
        refine ⟨80344626692820216058746809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53563084461880144039164539 80344626692820216058746809)
        ·
          refine ⟨60258470019615162044060107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80344626692820216058746809 60258470019615162044060107)
          ·
            refine ⟨90387705029422743066090161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60258470019615162044060107 90387705029422743066090161)
            ·
              refine ⟨67790778772067057299567621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90387705029422743066090161 67790778772067057299567621)
              ·
                refine ⟨12710771019762573243668929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67790778772067057299567621 12710771019762573243668929)
                ·
                  refine ⟨9533078264821929932751697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12710771019762573243668929 9533078264821929932751697)
                  ·
                    refine ⟨7149808698616447449563773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9533078264821929932751697 7149808698616447449563773)
                    ·
                      refine ⟨2681178261981167793586415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7149808698616447449563773 2681178261981167793586415)
                      ·
                        rfl

theorem cell23_5221576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 4, 2, 2, 3].length) (baseStart_5221576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5221576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5221576 prefixEnd_5221576 := by exact prefixLift 5221576
  have htrace : WordTrace (prefixWord ++ tailWord_5221576) baseStart_5221576 baseEnd_5221576 := by
    simpa [prefixWord, tailWord_5221576, baseEnd_5221576] using wordTrace_append hprefix tailTrace_5221576
  have hstable : (prefixWord ++ tailWord_5221576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5221576).length < 2 ^ (prefixWord ++ tailWord_5221576).sum := by decide
  have hdescent : baseEnd_5221576 < baseStart_5221576 := by decide
  rcases family_descends (prefixWord ++ tailWord_5221576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5221579 : List Nat := [1, 1, 1, 1, 3, 2, 2, 6, 6]
def baseStart_5221579 : Nat := 118140960795 + 5221579 * 2 ^ 59
def prefixEnd_5221579 : Nat := 4983230072969 + 3 ^ 40 * 5221579 * 2
def baseEnd_5221579 : Nat := 297908866935903475760989

theorem tailTrace_5221579 : CollatzResearch.WordTrace tailWord_5221579 prefixEnd_5221579 297908866935903475760989 := by
  unfold tailWord_5221579
  simp only [CollatzResearch.WordTrace]
  refine ⟨190446631950118532540499791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126964421300079021693666527 190446631950118532540499791)
  ·
    refine ⟨285669947925177798810749687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190446631950118532540499791 285669947925177798810749687)
    ·
      refine ⟨428504921887766698216124531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285669947925177798810749687 428504921887766698216124531)
      ·
        refine ⟨642757382831650047324186797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 428504921887766698216124531 642757382831650047324186797)
        ·
          refine ⟨241034018561868767746570049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 642757382831650047324186797 241034018561868767746570049)
          ·
            refine ⟨180775513921401575809927537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 241034018561868767746570049 180775513921401575809927537)
            ·
              refine ⟨135581635441051181857445653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 180775513921401575809927537 135581635441051181857445653)
              ·
                refine ⟨6355389161299274149567765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 135581635441051181857445653 6355389161299274149567765)
                ·
                  refine ⟨297908866935903475760989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6355389161299274149567765 297908866935903475760989)
                  ·
                    rfl

theorem cell23_5221579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 6, 6].length) (baseStart_5221579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5221579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5221579 prefixEnd_5221579 := by exact prefixLift 5221579
  have htrace : WordTrace (prefixWord ++ tailWord_5221579) baseStart_5221579 baseEnd_5221579 := by
    simpa [prefixWord, tailWord_5221579, baseEnd_5221579] using wordTrace_append hprefix tailTrace_5221579
  have hstable : (prefixWord ++ tailWord_5221579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5221579).length < 2 ^ (prefixWord ++ tailWord_5221579).sum := by decide
  have hdescent : baseEnd_5221579 < baseStart_5221579 := by decide
  rcases family_descends (prefixWord ++ tailWord_5221579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5221626 : List Nat := [3, 1, 1, 1, 1, 4, 1, 5, 1, 5]
def baseStart_5221626 : Nat := 118140960795 + 5221626 * 2 ^ 59
def prefixEnd_5221626 : Nat := 4983230072969 + 3 ^ 40 * 5221626 * 2
def baseEnd_5221626 : Nat := 893734645337964199320395

theorem tailTrace_5221626 : CollatzResearch.WordTrace tailWord_5221626 prefixEnd_5221626 893734645337964199320395 := by
  unfold tailWord_5221626
  simp only [CollatzResearch.WordTrace]
  refine ⟨47612086545237064891865183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126965564120632173044973821 47612086545237064891865183)
  ·
    refine ⟨71418129817855597337797775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47612086545237064891865183 71418129817855597337797775)
    ·
      refine ⟨107127194726783396006696663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71418129817855597337797775 107127194726783396006696663)
      ·
        refine ⟨160690792090175094010044995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107127194726783396006696663 160690792090175094010044995)
        ·
          refine ⟨241036188135262641015067493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160690792090175094010044995 241036188135262641015067493)
          ·
            refine ⟨45194285275361745190325155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 241036188135262641015067493 45194285275361745190325155)
            ·
              refine ⟨67791427913042617785487733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45194285275361745190325155 67791427913042617785487733)
              ·
                refine ⟨6355446366847745417389475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67791427913042617785487733 6355446366847745417389475)
                ·
                  refine ⟨9533169550271618126084213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6355446366847745417389475 9533169550271618126084213)
                  ·
                    refine ⟨893734645337964199320395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9533169550271618126084213 893734645337964199320395)
                    ·
                      rfl

theorem cell23_5221626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 5, 1, 5].length) (baseStart_5221626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5221626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5221626 prefixEnd_5221626 := by exact prefixLift 5221626
  have htrace : WordTrace (prefixWord ++ tailWord_5221626) baseStart_5221626 baseEnd_5221626 := by
    simpa [prefixWord, tailWord_5221626, baseEnd_5221626] using wordTrace_append hprefix tailTrace_5221626
  have hstable : (prefixWord ++ tailWord_5221626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5221626).length < 2 ^ (prefixWord ++ tailWord_5221626).sum := by decide
  have hdescent : baseEnd_5221626 < baseStart_5221626 := by decide
  rcases family_descends (prefixWord ++ tailWord_5221626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5221633 : List Nat := [1, 2, 4, 1, 1, 3, 1, 1, 4, 3, 2]
def baseStart_5221633 : Nat := 118140960795 + 5221633 * 2 ^ 59
def prefixEnd_5221633 : Nat := 4983230072969 + 3 ^ 40 * 5221633 * 2
def baseEnd_5221633 : Nat := 2681207530378474070573653

theorem tailTrace_5221633 : CollatzResearch.WordTrace tailWord_5221633 prefixEnd_5221633 2681207530378474070573653 := by
  unfold tailWord_5221633
  simp only [CollatzResearch.WordTrace]
  refine ⟨190448601491922899762965553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126965734327948599841977035 190448601491922899762965553)
  ·
    refine ⟨142836451118942174822224165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190448601491922899762965553 142836451118942174822224165)
    ·
      refine ⟨26781834584801657779167031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 142836451118942174822224165 26781834584801657779167031)
      ·
        refine ⟨40172751877202486668750547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26781834584801657779167031 40172751877202486668750547)
        ·
          refine ⟨60259127815803730003125821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40172751877202486668750547 60259127815803730003125821)
          ·
            refine ⟨22597172930926398751172183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60259127815803730003125821 22597172930926398751172183)
            ·
              refine ⟨33895759396389598126758275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22597172930926398751172183 33895759396389598126758275)
              ·
                refine ⟨50843639094584397190137413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33895759396389598126758275 50843639094584397190137413)
                ·
                  refine ⟨9533182330234574473150765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50843639094584397190137413 9533182330234574473150765)
                  ·
                    refine ⟨3574943373837965427431537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9533182330234574473150765 3574943373837965427431537)
                    ·
                      refine ⟨2681207530378474070573653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3574943373837965427431537 2681207530378474070573653)
                      ·
                        rfl

theorem cell23_5221633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 4, 3, 2].length) (baseStart_5221633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5221633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5221633 prefixEnd_5221633 := by exact prefixLift 5221633
  have htrace : WordTrace (prefixWord ++ tailWord_5221633) baseStart_5221633 baseEnd_5221633 := by
    simpa [prefixWord, tailWord_5221633, baseEnd_5221633] using wordTrace_append hprefix tailTrace_5221633
  have hstable : (prefixWord ++ tailWord_5221633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5221633).length < 2 ^ (prefixWord ++ tailWord_5221633).sum := by decide
  have hdescent : baseEnd_5221633 < baseStart_5221633 := by decide
  rcases family_descends (prefixWord ++ tailWord_5221633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5221634 : List Nat := [3, 4, 1, 1, 3, 1, 3, 2, 1, 4]
def baseStart_5221634 : Nat := 118140960795 + 5221634 * 2 ^ 59
def prefixEnd_5221634 : Nat := 4983230072969 + 3 ^ 40 * 5221634 * 2
def baseEnd_5221634 : Nat := 893736014619709522220383

theorem tailTrace_5221634 : CollatzResearch.WordTrace tailWord_5221634 prefixEnd_5221634 893736014619709522220383 := by
  unfold tailWord_5221634
  simp only [CollatzResearch.WordTrace]
  refine ⟨47612159491229819233437989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126965758643279517955834637 47612159491229819233437989)
  ·
    refine ⟨8927279904605591106269623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47612159491229819233437989 8927279904605591106269623)
    ·
      refine ⟨13390919856908386659404435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8927279904605591106269623 13390919856908386659404435)
      ·
        refine ⟨20086379785362579989106653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13390919856908386659404435 20086379785362579989106653)
        ·
          refine ⟨7532392419510967495914995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20086379785362579989106653 7532392419510967495914995)
          ·
            refine ⟨11298588629266451243872493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7532392419510967495914995 11298588629266451243872493)
            ·
              refine ⟨4236970735974919216452185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11298588629266451243872493 4236970735974919216452185)
              ·
                refine ⟨3177728051981189412339139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4236970735974919216452185 3177728051981189412339139)
                ·
                  refine ⟨4766592077971784118508709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3177728051981189412339139 4766592077971784118508709)
                  ·
                    refine ⟨893736014619709522220383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4766592077971784118508709 893736014619709522220383)
                    ·
                      rfl

theorem cell23_5221634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_5221634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5221634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5221634 prefixEnd_5221634 := by exact prefixLift 5221634
  have htrace : WordTrace (prefixWord ++ tailWord_5221634) baseStart_5221634 baseEnd_5221634 := by
    simpa [prefixWord, tailWord_5221634, baseEnd_5221634] using wordTrace_append hprefix tailTrace_5221634
  have hstable : (prefixWord ++ tailWord_5221634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5221634).length < 2 ^ (prefixWord ++ tailWord_5221634).sum := by decide
  have hdescent : baseEnd_5221634 < baseStart_5221634 := by decide
  rcases family_descends (prefixWord ++ tailWord_5221634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5221663 : List Nat := [1, 1, 2, 4, 4, 1, 1, 1, 3, 1, 4]
def baseStart_5221663 : Nat := 118140960795 + 5221663 * 2 ^ 59
def prefixEnd_5221663 : Nat := 4983230072969 + 3 ^ 40 * 5221663 * 2
def baseEnd_5221663 : Nat := 2681222934798108953198515

theorem tailTrace_5221663 : CollatzResearch.WordTrace tailWord_5221663 prefixEnd_5221663 2681222934798108953198515 := by
  unfold tailWord_5221663
  simp only [CollatzResearch.WordTrace]
  refine ⟨190449695681814214886557643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126966463787876143257705095 190449695681814214886557643)
  ·
    refine ⟨285674543522721322329836465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190449695681814214886557643 285674543522721322329836465)
    ·
      refine ⟨214255907642040991747377349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 285674543522721322329836465 214255907642040991747377349)
      ·
        refine ⟨40172982682882685952633253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 214255907642040991747377349 40172982682882685952633253)
        ·
          refine ⟨7532434253040503616118735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40172982682882685952633253 7532434253040503616118735)
          ·
            refine ⟨11298651379560755424178103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7532434253040503616118735 11298651379560755424178103)
            ·
              refine ⟨16947977069341133136267155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11298651379560755424178103 16947977069341133136267155)
              ·
                refine ⟨25421965604011699704400733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16947977069341133136267155 25421965604011699704400733)
                ·
                  refine ⟨9533237101504387389150275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25421965604011699704400733 9533237101504387389150275)
                  ·
                    refine ⟨14299855652256581083725413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9533237101504387389150275 14299855652256581083725413)
                    ·
                      refine ⟨2681222934798108953198515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14299855652256581083725413 2681222934798108953198515)
                      ·
                        rfl

theorem cell23_5221663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 3, 1, 4].length) (baseStart_5221663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5221663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5221663 prefixEnd_5221663 := by exact prefixLift 5221663
  have htrace : WordTrace (prefixWord ++ tailWord_5221663) baseStart_5221663 baseEnd_5221663 := by
    simpa [prefixWord, tailWord_5221663, baseEnd_5221663] using wordTrace_append hprefix tailTrace_5221663
  have hstable : (prefixWord ++ tailWord_5221663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5221663).length < 2 ^ (prefixWord ++ tailWord_5221663).sum := by decide
  have hdescent : baseEnd_5221663 < baseStart_5221663 := by decide
  rcases family_descends (prefixWord ++ tailWord_5221663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5221677 : List Nat := [1, 5, 3, 1, 1, 2, 3, 1, 1, 5]
def baseStart_5221677 : Nat := 118140960795 + 5221677 * 2 ^ 59
def prefixEnd_5221677 : Nat := 4983230072969 + 3 ^ 40 * 5221677 * 2
def baseEnd_5221677 : Nat := 893743374509090632807817

theorem tailTrace_5221677 : CollatzResearch.WordTrace tailWord_5221677 prefixEnd_5221677 893743374509090632807817 := by
  unfold tailWord_5221677
  simp only [CollatzResearch.WordTrace]
  refine ⟨190450206303763495277567285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126966804202508996851711523 190450206303763495277567285)
  ·
    refine ⟨17854706840977827682271933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 190450206303763495277567285 17854706840977827682271933)
    ·
      refine ⟨6695515065366685380851975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17854706840977827682271933 6695515065366685380851975)
      ·
        refine ⟨10043272598050028071277963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6695515065366685380851975 10043272598050028071277963)
        ·
          refine ⟨15064908897075042106916945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10043272598050028071277963 15064908897075042106916945)
          ·
            refine ⟨11298681672806281580187709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15064908897075042106916945 11298681672806281580187709)
            ·
              refine ⟨4237005627302355592570391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11298681672806281580187709 4237005627302355592570391)
              ·
                refine ⟨6355508440953533388855587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4237005627302355592570391 6355508440953533388855587)
                ·
                  refine ⟨9533262661430300083283381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6355508440953533388855587 9533262661430300083283381)
                  ·
                    refine ⟨893743374509090632807817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9533262661430300083283381 893743374509090632807817)
                    ·
                      rfl

theorem cell23_5221677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_5221677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5221677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5221677 prefixEnd_5221677 := by exact prefixLift 5221677
  have htrace : WordTrace (prefixWord ++ tailWord_5221677) baseStart_5221677 baseEnd_5221677 := by
    simpa [prefixWord, tailWord_5221677, baseEnd_5221677] using wordTrace_append hprefix tailTrace_5221677
  have hstable : (prefixWord ++ tailWord_5221677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5221677).length < 2 ^ (prefixWord ++ tailWord_5221677).sum := by decide
  have hdescent : baseEnd_5221677 < baseStart_5221677 := by decide
  rcases family_descends (prefixWord ++ tailWord_5221677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5221683 : List Nat := [1, 1, 1, 2, 5, 4, 1, 1, 1, 1, 5]
def baseStart_5221683 : Nat := 118140960795 + 5221683 * 2 ^ 59
def prefixEnd_5221683 : Nat := 4983230072969 + 3 ^ 40 * 5221683 * 2
def baseEnd_5221683 : Nat := 2681233204411198874948423

theorem tailTrace_5221683 : CollatzResearch.WordTrace tailWord_5221683 prefixEnd_5221683 2681233204411198874948423 := by
  unfold tailWord_5221683
  simp only [CollatzResearch.WordTrace]
  refine ⟨190450425141741758302285703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126966950094494505534857135 190450425141741758302285703)
  ·
    refine ⟨285675637712612637453428555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190450425141741758302285703 285675637712612637453428555)
    ·
      refine ⟨428513456568918956180142833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285675637712612637453428555 428513456568918956180142833)
      ·
        refine ⟨321385092426689217135107125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 428513456568918956180142833 321385092426689217135107125)
        ·
          refine ⟨30129852415002114106416293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 321385092426689217135107125 30129852415002114106416293)
          ·
            refine ⟨5649347327812896394953055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30129852415002114106416293 5649347327812896394953055)
            ·
              refine ⟨8474020991719344592429583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5649347327812896394953055 8474020991719344592429583)
              ·
                refine ⟨12711031487579016888644375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8474020991719344592429583 12711031487579016888644375)
                ·
                  refine ⟨19066547231368525332966563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12711031487579016888644375 19066547231368525332966563)
                  ·
                    refine ⟨28599820847052787999449845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19066547231368525332966563 28599820847052787999449845)
                    ·
                      refine ⟨2681233204411198874948423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28599820847052787999449845 2681233204411198874948423)
                      ·
                        rfl

theorem cell23_5221683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 1, 1, 1, 5].length) (baseStart_5221683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5221683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5221683 prefixEnd_5221683 := by exact prefixLift 5221683
  have htrace : WordTrace (prefixWord ++ tailWord_5221683) baseStart_5221683 baseEnd_5221683 := by
    simpa [prefixWord, tailWord_5221683, baseEnd_5221683] using wordTrace_append hprefix tailTrace_5221683
  have hstable : (prefixWord ++ tailWord_5221683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5221683).length < 2 ^ (prefixWord ++ tailWord_5221683).sum := by decide
  have hdescent : baseEnd_5221683 < baseStart_5221683 := by decide
  rcases family_descends (prefixWord ++ tailWord_5221683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5221696 : List Nat := [2, 1, 1, 2, 2, 1, 3, 2, 3, 3, 3]
def baseStart_5221696 : Nat := 118140960795 + 5221696 * 2 ^ 59
def prefixEnd_5221696 : Nat := 4983230072969 + 3 ^ 40 * 5221696 * 2
def baseEnd_5221696 : Nat := 2681239879659707324085863

theorem tailTrace_5221696 : CollatzResearch.WordTrace tailWord_5221696 prefixEnd_5221696 2681239879659707324085863 := by
  unfold tailWord_5221696
  simp only [CollatzResearch.WordTrace]
  refine ⟨95225449645347330761254471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126967266193796441015005961 95225449645347330761254471)
  ·
    refine ⟨142838174468020996141881707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95225449645347330761254471 142838174468020996141881707)
    ·
      refine ⟨214257261702031494212822561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142838174468020996141881707 214257261702031494212822561)
      ·
        refine ⟨160692946276523620659616921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214257261702031494212822561 160692946276523620659616921)
        ·
          refine ⟨120519709707392715494712691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160692946276523620659616921 120519709707392715494712691)
          ·
            refine ⟨180779564561089073242069037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120519709707392715494712691 180779564561089073242069037)
            ·
              refine ⟨67792336710408402465775889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 180779564561089073242069037 67792336710408402465775889)
              ·
                refine ⟨50844252532806301849331917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67792336710408402465775889 50844252532806301849331917)
                ·
                  refine ⟨19066594699802363193499469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50844252532806301849331917 19066594699802363193499469)
                  ·
                    refine ⟨7149973012425886197562301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19066594699802363193499469 7149973012425886197562301)
                    ·
                      refine ⟨2681239879659707324085863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7149973012425886197562301 2681239879659707324085863)
                      ·
                        rfl

theorem cell23_5221696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 3, 3, 3].length) (baseStart_5221696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5221696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5221696 prefixEnd_5221696 := by exact prefixLift 5221696
  have htrace : WordTrace (prefixWord ++ tailWord_5221696) baseStart_5221696 baseEnd_5221696 := by
    simpa [prefixWord, tailWord_5221696, baseEnd_5221696] using wordTrace_append hprefix tailTrace_5221696
  have hstable : (prefixWord ++ tailWord_5221696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5221696).length < 2 ^ (prefixWord ++ tailWord_5221696).sum := by decide
  have hdescent : baseEnd_5221696 < baseStart_5221696 := by decide
  rcases family_descends (prefixWord ++ tailWord_5221696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5221700 : List Nat := [2, 3, 4, 1, 1, 1, 1, 2, 3, 2, 3]
def baseStart_5221700 : Nat := 118140960795 + 5221700 * 2 ^ 59
def prefixEnd_5221700 : Nat := 4983230072969 + 3 ^ 40 * 5221700 * 2
def baseEnd_5221700 : Nat := 2681241933582325308435845

theorem tailTrace_5221700 : CollatzResearch.WordTrace tailWord_5221700 prefixEnd_5221700 2681241933582325308435845 := by
  unfold tailWord_5221700
  simp only [CollatzResearch.WordTrace]
  refine ⟨95225522591340085102827277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126967363455120113470436369 95225522591340085102827277)
  ·
    refine ⟨35709570971752531913560229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95225522591340085102827277 35709570971752531913560229)
    ·
      refine ⟨6695544557203599733792543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35709570971752531913560229 6695544557203599733792543)
      ·
        refine ⟨10043316835805399600688815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6695544557203599733792543 10043316835805399600688815)
        ·
          refine ⟨15064975253708099401033223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10043316835805399600688815 15064975253708099401033223)
          ·
            refine ⟨22597462880562149101549835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15064975253708099401033223 22597462880562149101549835)
            ·
              refine ⟨33896194320843223652324753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22597462880562149101549835 33896194320843223652324753)
              ·
                refine ⟨25422145740632417739243565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33896194320843223652324753 25422145740632417739243565)
                ·
                  refine ⟨9533304652737156652216337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25422145740632417739243565 9533304652737156652216337)
                  ·
                    refine ⟨7149978489552867489162253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9533304652737156652216337 7149978489552867489162253)
                    ·
                      refine ⟨2681241933582325308435845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7149978489552867489162253 2681241933582325308435845)
                      ·
                        rfl

theorem cell23_5221700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_5221700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5221700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5221700 prefixEnd_5221700 := by exact prefixLift 5221700
  have htrace : WordTrace (prefixWord ++ tailWord_5221700) baseStart_5221700 baseEnd_5221700 := by
    simpa [prefixWord, tailWord_5221700, baseEnd_5221700] using wordTrace_append hprefix tailTrace_5221700
  have hstable : (prefixWord ++ tailWord_5221700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5221700).length < 2 ^ (prefixWord ++ tailWord_5221700).sum := by decide
  have hdescent : baseEnd_5221700 < baseStart_5221700 := by decide
  rcases family_descends (prefixWord ++ tailWord_5221700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5221713 : List Nat := [1, 2, 2, 1, 4, 1, 4, 1, 1, 3, 3]
def baseStart_5221713 : Nat := 118140960795 + 5221713 * 2 ^ 59
def prefixEnd_5221713 : Nat := 4983230072969 + 3 ^ 40 * 5221713 * 2
def baseEnd_5221713 : Nat := 2681248608830833757573285

theorem tailTrace_5221713 : CollatzResearch.WordTrace tailWord_5221713 prefixEnd_5221713 2681248608830833757573285 := by
  unfold tailWord_5221713
  simp only [CollatzResearch.WordTrace]
  refine ⟨190451519331633073425877793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126967679554422048950585195 190451519331633073425877793)
  ·
    refine ⟨142838639498724805069408345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190451519331633073425877793 142838639498724805069408345)
    ·
      refine ⟨107128979624043603802056259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142838639498724805069408345 107128979624043603802056259)
      ·
        refine ⟨160693469436065405703084389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107128979624043603802056259 160693469436065405703084389)
        ·
          refine ⟨30130025519262263569328323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 160693469436065405703084389 30130025519262263569328323)
          ·
            refine ⟨45195038278893395353992485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30130025519262263569328323 45195038278893395353992485)
            ·
              refine ⟨8474069677292511628873591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45195038278893395353992485 8474069677292511628873591)
              ·
                refine ⟨12711104515938767443310387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8474069677292511628873591 12711104515938767443310387)
                ·
                  refine ⟨19066656773908151164965581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12711104515938767443310387 19066656773908151164965581)
                  ·
                    refine ⟨7149996290215556686862093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19066656773908151164965581 7149996290215556686862093)
                    ·
                      refine ⟨2681248608830833757573285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7149996290215556686862093 2681248608830833757573285)
                      ·
                        rfl

theorem cell23_5221713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 1, 1, 3, 3].length) (baseStart_5221713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5221713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5221713 prefixEnd_5221713 := by exact prefixLift 5221713
  have htrace : WordTrace (prefixWord ++ tailWord_5221713) baseStart_5221713 baseEnd_5221713 := by
    simpa [prefixWord, tailWord_5221713, baseEnd_5221713] using wordTrace_append hprefix tailTrace_5221713
  have hstable : (prefixWord ++ tailWord_5221713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5221713).length < 2 ^ (prefixWord ++ tailWord_5221713).sum := by decide
  have hdescent : baseEnd_5221713 < baseStart_5221713 := by decide
  rcases family_descends (prefixWord ++ tailWord_5221713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5221716 : List Nat := [2, 4, 1, 1, 2, 1, 1, 2, 2, 7]
def baseStart_5221716 : Nat := 118140960795 + 5221716 * 2 ^ 59
def prefixEnd_5221716 : Nat := 4983230072969 + 3 ^ 40 * 5221716 * 2
def baseEnd_5221716 : Nat := 893750049757599081945257

theorem tailTrace_5221716 : CollatzResearch.WordTrace tailWord_5221716 prefixEnd_5221716 893750049757599081945257 := by
  unfold tailWord_5221716
  simp only [CollatzResearch.WordTrace]
  refine ⟨95225814375311102469118501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126967752500414803292158001 95225814375311102469118501)
  ·
    refine ⟨17854840195370831712959719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95225814375311102469118501 17854840195370831712959719)
    ·
      refine ⟨26782260293056247569439579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17854840195370831712959719 26782260293056247569439579)
      ·
        refine ⟨40173390439584371354159369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26782260293056247569439579 40173390439584371354159369)
        ·
          refine ⟨30130042829688278515619527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40173390439584371354159369 30130042829688278515619527)
          ·
            refine ⟨45195064244532417773429291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30130042829688278515619527 45195064244532417773429291)
            ·
              refine ⟨67792596366798626660143937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45195064244532417773429291 67792596366798626660143937)
              ·
                refine ⟨50844447275098969995107953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67792596366798626660143937 50844447275098969995107953)
                ·
                  refine ⟨38133335456324227496330965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50844447275098969995107953 38133335456324227496330965)
                  ·
                    refine ⟨893750049757599081945257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38133335456324227496330965 893750049757599081945257)
                    ·
                      rfl

theorem cell23_5221716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_5221716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5221716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5221716 prefixEnd_5221716 := by exact prefixLift 5221716
  have htrace : WordTrace (prefixWord ++ tailWord_5221716) baseStart_5221716 baseEnd_5221716 := by
    simpa [prefixWord, tailWord_5221716, baseEnd_5221716] using wordTrace_append hprefix tailTrace_5221716
  have hstable : (prefixWord ++ tailWord_5221716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5221716).length < 2 ^ (prefixWord ++ tailWord_5221716).sum := by decide
  have hdescent : baseEnd_5221716 < baseStart_5221716 := by decide
  rcases family_descends (prefixWord ++ tailWord_5221716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5221718 : List Nat := [5, 2, 3, 1, 1, 2, 1, 1, 2, 3, 2]
def baseStart_5221718 : Nat := 118140960795 + 5221718 * 2 ^ 59
def prefixEnd_5221718 : Nat := 4983230072969 + 3 ^ 40 * 5221718 * 2
def baseEnd_5221718 : Nat := 2681251176234106238010763

theorem tailTrace_5221718 : CollatzResearch.WordTrace tailWord_5221718 prefixEnd_5221718 2681251176234106238010763 := by
  unfold tailWord_5221718
  simp only [CollatzResearch.WordTrace]
  refine ⟨11903231356038434954988113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 126967801131076639519873205 11903231356038434954988113)
  ·
    refine ⟨8927423517028826216241085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11903231356038434954988113 8927423517028826216241085)
    ·
      refine ⟨3347783818885809831090407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8927423517028826216241085 3347783818885809831090407)
      ·
        refine ⟨5021675728328714746635611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3347783818885809831090407 5021675728328714746635611)
        ·
          refine ⟨7532513592493072119953417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5021675728328714746635611 7532513592493072119953417)
          ·
            refine ⟨5649385194369804089965063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7532513592493072119953417 5649385194369804089965063)
            ·
              refine ⟨8474077791554706134947595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5649385194369804089965063 8474077791554706134947595)
              ·
                refine ⟨12711116687332059202421393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8474077791554706134947595 12711116687332059202421393)
                ·
                  refine ⟨9533337515499044401816045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12711116687332059202421393 9533337515499044401816045)
                  ·
                    refine ⟨3575001568312141650681017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9533337515499044401816045 3575001568312141650681017)
                    ·
                      refine ⟨2681251176234106238010763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3575001568312141650681017 2681251176234106238010763)
                      ·
                        rfl

theorem cell23_5221718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_5221718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5221718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5221718 prefixEnd_5221718 := by exact prefixLift 5221718
  have htrace : WordTrace (prefixWord ++ tailWord_5221718) baseStart_5221718 baseEnd_5221718 := by
    simpa [prefixWord, tailWord_5221718, baseEnd_5221718] using wordTrace_append hprefix tailTrace_5221718
  have hstable : (prefixWord ++ tailWord_5221718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5221718).length < 2 ^ (prefixWord ++ tailWord_5221718).sum := by decide
  have hdescent : baseEnd_5221718 < baseStart_5221718 := by decide
  rcases family_descends (prefixWord ++ tailWord_5221718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5221730 : List Nat := [3, 3, 2, 1, 1, 1, 2, 2, 4, 1, 3]
def baseStart_5221730 : Nat := 118140960795 + 5221730 * 2 ^ 59
def prefixEnd_5221730 : Nat := 4983230072969 + 3 ^ 40 * 5221730 * 2
def baseEnd_5221730 : Nat := 2681257338001960191060707

theorem tailTrace_5221730 : CollatzResearch.WordTrace tailWord_5221730 prefixEnd_5221730 2681257338001960191060707 := by
  unfold tailWord_5221730
  simp only [CollatzResearch.WordTrace]
  refine ⟨47613034843142871332311661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126968092915047656886164429 47613034843142871332311661)
  ·
    refine ⟨17854888066178576749616873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47613034843142871332311661 17854888066178576749616873)
    ·
      refine ⟨13391166049633932562212655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17854888066178576749616873 13391166049633932562212655)
      ·
        refine ⟨20086749074450898843318983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13391166049633932562212655 20086749074450898843318983)
        ·
          refine ⟨30130123611676348264978475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20086749074450898843318983 30130123611676348264978475)
          ·
            refine ⟨45195185417514522397467713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30130123611676348264978475 45195185417514522397467713)
            ·
              refine ⟨33896389063135891798100785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45195185417514522397467713 33896389063135891798100785)
              ·
                refine ⟨25422291797351918848575589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33896389063135891798100785 25422291797351918848575589)
                ·
                  refine ⟨4766679712003484784107923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25422291797351918848575589 4766679712003484784107923)
                  ·
                    refine ⟨7150019568005227176161885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4766679712003484784107923 7150019568005227176161885)
                    ·
                      refine ⟨2681257338001960191060707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7150019568005227176161885 2681257338001960191060707)
                      ·
                        rfl

theorem cell23_5221730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_5221730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5221730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5221730 prefixEnd_5221730 := by exact prefixLift 5221730
  have htrace : WordTrace (prefixWord ++ tailWord_5221730) baseStart_5221730 baseEnd_5221730 := by
    simpa [prefixWord, tailWord_5221730, baseEnd_5221730] using wordTrace_append hprefix tailTrace_5221730
  have hstable : (prefixWord ++ tailWord_5221730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5221730).length < 2 ^ (prefixWord ++ tailWord_5221730).sum := by decide
  have hdescent : baseEnd_5221730 < baseStart_5221730 := by decide
  rcases family_descends (prefixWord ++ tailWord_5221730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5221746 : List Nat := [3, 2, 1, 2, 1, 2, 1, 1, 4, 6]
def baseStart_5221746 : Nat := 118140960795 + 5221746 * 2 ^ 59
def prefixEnd_5221746 : Nat := 4983230072969 + 3 ^ 40 * 5221746 * 2
def baseEnd_5221746 : Nat := 893755184564144042820211

theorem tailTrace_5221746 : CollatzResearch.WordTrace tailWord_5221746 prefixEnd_5221746 893755184564144042820211 := by
  unfold tailWord_5221746
  simp only [CollatzResearch.WordTrace]
  refine ⟨47613180735128380015457273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126968481960342346707886061 47613180735128380015457273)
  ·
    refine ⟨35709885551346285011592955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47613180735128380015457273 35709885551346285011592955)
    ·
      refine ⟨53564828327019427517389433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35709885551346285011592955 53564828327019427517389433)
      ·
        refine ⟨40173621245264570638042075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53564828327019427517389433 40173621245264570638042075)
        ·
          refine ⟨60260431867896855957063113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40173621245264570638042075 60260431867896855957063113)
          ·
            refine ⟨45195323900922641967797335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60260431867896855957063113 45195323900922641967797335)
            ·
              refine ⟨67792985851383962951696003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45195323900922641967797335 67792985851383962951696003)
              ·
                refine ⟨101689478777075944427544005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67792985851383962951696003 101689478777075944427544005)
                ·
                  refine ⟨19066777270701739580164501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 101689478777075944427544005 19066777270701739580164501)
                  ·
                    refine ⟨893755184564144042820211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19066777270701739580164501 893755184564144042820211)
                    ·
                      rfl

theorem cell23_5221746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 4, 6].length) (baseStart_5221746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5221746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5221746 prefixEnd_5221746 := by exact prefixLift 5221746
  have htrace : WordTrace (prefixWord ++ tailWord_5221746) baseStart_5221746 baseEnd_5221746 := by
    simpa [prefixWord, tailWord_5221746, baseEnd_5221746] using wordTrace_append hprefix tailTrace_5221746
  have hstable : (prefixWord ++ tailWord_5221746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5221746).length < 2 ^ (prefixWord ++ tailWord_5221746).sum := by decide
  have hdescent : baseEnd_5221746 < baseStart_5221746 := by decide
  rcases family_descends (prefixWord ++ tailWord_5221746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5221753 : List Nat := [1, 2, 1, 3, 2, 1, 2, 2, 3, 4, 2]
def baseStart_5221753 : Nat := 118140960795 + 5221753 * 2 ^ 59
def prefixEnd_5221753 : Nat := 4983230072969 + 3 ^ 40 * 5221753 * 2
def baseEnd_5221753 : Nat := 2681269148057013601073101

theorem tailTrace_5221753 : CollatzResearch.WordTrace tailWord_5221753 prefixEnd_5221753 2681269148057013601073101 := by
  unfold tailWord_5221753
  simp only [CollatzResearch.WordTrace]
  refine ⟨190452978251488160257333913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126968652167658773504889275 190452978251488160257333913)
  ·
    refine ⟨142839733688616120193000435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190452978251488160257333913 142839733688616120193000435)
    ·
      refine ⟨214259600532924180289500653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142839733688616120193000435 214259600532924180289500653)
      ·
        refine ⟨80347350199846567608562745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 214259600532924180289500653 80347350199846567608562745)
        ·
          refine ⟨60260512649884925706422059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80347350199846567608562745 60260512649884925706422059)
          ·
            refine ⟨90390768974827388559633089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60260512649884925706422059 90390768974827388559633089)
            ·
              refine ⟨67793076731120541419724817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90390768974827388559633089 67793076731120541419724817)
              ·
                refine ⟨50844807548340406064793613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67793076731120541419724817 50844807548340406064793613)
                ·
                  refine ⟨19066802830627652274297605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50844807548340406064793613 19066802830627652274297605)
                  ·
                    refine ⟨3575025530742684801430801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19066802830627652274297605 3575025530742684801430801)
                    ·
                      refine ⟨2681269148057013601073101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3575025530742684801430801 2681269148057013601073101)
                      ·
                        rfl

theorem cell23_5221753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 3, 4, 2].length) (baseStart_5221753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5221753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5221753 prefixEnd_5221753 := by exact prefixLift 5221753
  have htrace : WordTrace (prefixWord ++ tailWord_5221753) baseStart_5221753 baseEnd_5221753 := by
    simpa [prefixWord, tailWord_5221753, baseEnd_5221753] using wordTrace_append hprefix tailTrace_5221753
  have hstable : (prefixWord ++ tailWord_5221753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5221753).length < 2 ^ (prefixWord ++ tailWord_5221753).sum := by decide
  have hdescent : baseEnd_5221753 < baseStart_5221753 := by decide
  rcases family_descends (prefixWord ++ tailWord_5221753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5221774 : List Nat := [4, 1, 1, 4, 2, 1, 2, 2, 1, 3, 2]
def baseStart_5221774 : Nat := 118140960795 + 5221774 * 2 ^ 59
def prefixEnd_5221774 : Nat := 4983230072969 + 3 ^ 40 * 5221774 * 2
def baseEnd_5221774 : Nat := 2681279931150758018910505

theorem tailTrace_5221774 : CollatzResearch.WordTrace tailWord_5221774 prefixEnd_5221774 2681279931150758018910505 := by
  unfold tailWord_5221774
  simp only [CollatzResearch.WordTrace]
  refine ⟨23806718023051510105481047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126969162789608053895898917 23806718023051510105481047)
  ·
    refine ⟨35710077034577265158221571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23806718023051510105481047 35710077034577265158221571)
    ·
      refine ⟨53565115551865897737332357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35710077034577265158221571 53565115551865897737332357)
      ·
        refine ⟨10043459165974855825749817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53565115551865897737332357 10043459165974855825749817)
        ·
          refine ⟨7532594374481141869312363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10043459165974855825749817 7532594374481141869312363)
          ·
            refine ⟨11298891561721712803968545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7532594374481141869312363 11298891561721712803968545)
            ·
              refine ⟨8474168671291284602976409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11298891561721712803968545 8474168671291284602976409)
              ·
                refine ⟨6355626503468463452232307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8474168671291284602976409 6355626503468463452232307)
                ·
                  refine ⟨9533439755202695178348461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6355626503468463452232307 9533439755202695178348461)
                  ·
                    refine ⟨3575039908201010691880673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9533439755202695178348461 3575039908201010691880673)
                    ·
                      refine ⟨2681279931150758018910505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3575039908201010691880673 2681279931150758018910505)
                      ·
                        rfl

theorem cell23_5221774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_5221774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5221774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5221774 prefixEnd_5221774 := by exact prefixLift 5221774
  have htrace : WordTrace (prefixWord ++ tailWord_5221774) baseStart_5221774 baseEnd_5221774 := by
    simpa [prefixWord, tailWord_5221774, baseEnd_5221774] using wordTrace_append hprefix tailTrace_5221774
  have hstable : (prefixWord ++ tailWord_5221774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5221774).length < 2 ^ (prefixWord ++ tailWord_5221774).sum := by decide
  have hdescent : baseEnd_5221774 < baseStart_5221774 := by decide
  rcases family_descends (prefixWord ++ tailWord_5221774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5221816 : List Nat := [2, 1, 2, 1, 2, 2, 3, 1, 1, 1, 7]
def baseStart_5221816 : Nat := 118140960795 + 5221816 * 2 ^ 59
def prefixEnd_5221816 : Nat := 4983230072969 + 3 ^ 40 * 5221816 * 2
def baseEnd_5221816 : Nat := 2681301497338246854585311

theorem tailTrace_5221816 : CollatzResearch.WordTrace tailWord_5221816 prefixEnd_5221816 2681301497338246854585311 := by
  unfold tailWord_5221816
  simp only [CollatzResearch.WordTrace]
  refine ⟨95227638025129961008438651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126970184033506614677918201 95227638025129961008438651)
  ·
    refine ⟨142841457037694941512657977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95227638025129961008438651 142841457037694941512657977)
    ·
      refine ⟨107131092778271206134493483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142841457037694941512657977 107131092778271206134493483)
      ·
        refine ⟨160696639167406809201740225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107131092778271206134493483 160696639167406809201740225)
        ·
          refine ⟨120522479375555106901305169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160696639167406809201740225 120522479375555106901305169)
          ·
            refine ⟨90391859531666330175978877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120522479375555106901305169 90391859531666330175978877)
            ·
              refine ⟨33896947324374873815992079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90391859531666330175978877 33896947324374873815992079)
              ·
                refine ⟨50845420986562310723988119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33896947324374873815992079 50845420986562310723988119)
                ·
                  refine ⟨76268131479843466085982179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50845420986562310723988119 76268131479843466085982179)
                  ·
                    refine ⟨114402197219765199128973269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 76268131479843466085982179 114402197219765199128973269)
                    ·
                      refine ⟨2681301497338246854585311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 114402197219765199128973269 2681301497338246854585311)
                      ·
                        rfl

theorem cell23_5221816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 1, 1, 7].length) (baseStart_5221816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5221816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5221816 prefixEnd_5221816 := by exact prefixLift 5221816
  have htrace : WordTrace (prefixWord ++ tailWord_5221816) baseStart_5221816 baseEnd_5221816 := by
    simpa [prefixWord, tailWord_5221816, baseEnd_5221816] using wordTrace_append hprefix tailTrace_5221816
  have hstable : (prefixWord ++ tailWord_5221816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5221816).length < 2 ^ (prefixWord ++ tailWord_5221816).sum := by decide
  have hdescent : baseEnd_5221816 < baseStart_5221816 := by decide
  rcases family_descends (prefixWord ++ tailWord_5221816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5221870 : List Nat := [4, 1, 2, 1, 2, 1, 2, 3, 3, 4]
def baseStart_5221870 : Nat := 118140960795 + 5221870 * 2 ^ 59
def prefixEnd_5221870 : Nat := 4983230072969 + 3 ^ 40 * 5221870 * 2
def baseEnd_5221870 : Nat := 893776408431196547770021

theorem tailTrace_5221870 : CollatzResearch.WordTrace tailWord_5221870 prefixEnd_5221870 893776408431196547770021 := by
  unfold tailWord_5221870
  simp only [CollatzResearch.WordTrace]
  refine ⟨23807155699008036154917883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126971497061376192826228709 23807155699008036154917883)
  ·
    refine ⟨35710733548512054232376825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23807155699008036154917883 35710733548512054232376825)
    ·
      refine ⟨26783050161384040674282619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35710733548512054232376825 26783050161384040674282619)
      ·
        refine ⟨40174575242076061011423929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26783050161384040674282619 40174575242076061011423929)
        ·
          refine ⟨30130931431557045758567947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40174575242076061011423929 30130931431557045758567947)
          ·
            refine ⟨45196397147335568637851921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30130931431557045758567947 45196397147335568637851921)
            ·
              refine ⟨33897297860501676478388941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45196397147335568637851921 33897297860501676478388941)
              ·
                refine ⟨12711486697688128679395853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33897297860501676478388941 12711486697688128679395853)
                ·
                  refine ⟨4766807511633048254773445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12711486697688128679395853 4766807511633048254773445)
                  ·
                    refine ⟨893776408431196547770021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4766807511633048254773445 893776408431196547770021)
                    ·
                      rfl

theorem cell23_5221870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 3, 3, 4].length) (baseStart_5221870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5221870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5221870 prefixEnd_5221870 := by exact prefixLift 5221870
  have htrace : WordTrace (prefixWord ++ tailWord_5221870) baseStart_5221870 baseEnd_5221870 := by
    simpa [prefixWord, tailWord_5221870, baseEnd_5221870] using wordTrace_append hprefix tailTrace_5221870
  have hstable : (prefixWord ++ tailWord_5221870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5221870).length < 2 ^ (prefixWord ++ tailWord_5221870).sum := by decide
  have hdescent : baseEnd_5221870 < baseStart_5221870 := by decide
  rcases family_descends (prefixWord ++ tailWord_5221870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5221877 : List Nat := [1, 3, 5, 1, 1, 1, 1, 1, 1, 6, 2]
def baseStart_5221877 : Nat := 118140960795 + 5221877 * 2 ^ 59
def prefixEnd_5221877 : Nat := 4983230072969 + 3 ^ 40 * 5221877 * 2
def baseEnd_5221877 : Nat := 2681332819658171115922531

theorem tailTrace_5221877 : CollatzResearch.WordTrace tailWord_5221877 prefixEnd_5221877 2681332819658171115922531 := by
  unfold tailWord_5221877
  simp only [CollatzResearch.WordTrace]
  refine ⟨190457500903038929434847885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126971667268692619623231923 190457500903038929434847885)
  ·
    refine ⟨71421562838639598538067957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190457500903038929434847885 71421562838639598538067957)
    ·
      refine ⟨6695771516122462362943871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 71421562838639598538067957 6695771516122462362943871)
      ·
        refine ⟨10043657274183693544415807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6695771516122462362943871 10043657274183693544415807)
        ·
          refine ⟨15065485911275540316623711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10043657274183693544415807 15065485911275540316623711)
          ·
            refine ⟨22598228866913310474935567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15065485911275540316623711 22598228866913310474935567)
            ·
              refine ⟨33897343300369965712403351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22598228866913310474935567 33897343300369965712403351)
              ·
                refine ⟨50846014950554948568605027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33897343300369965712403351 50846014950554948568605027)
                ·
                  refine ⟨76269022425832422852907541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50846014950554948568605027 76269022425832422852907541)
                  ·
                    refine ⟨3575110426210894821230041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 76269022425832422852907541 3575110426210894821230041)
                    ·
                      refine ⟨2681332819658171115922531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3575110426210894821230041 2681332819658171115922531)
                      ·
                        rfl

theorem cell23_5221877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_5221877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5221877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5221877 prefixEnd_5221877 := by exact prefixLift 5221877
  have htrace : WordTrace (prefixWord ++ tailWord_5221877) baseStart_5221877 baseEnd_5221877 := by
    simpa [prefixWord, tailWord_5221877, baseEnd_5221877] using wordTrace_append hprefix tailTrace_5221877
  have hstable : (prefixWord ++ tailWord_5221877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5221877).length < 2 ^ (prefixWord ++ tailWord_5221877).sum := by decide
  have hdescent : baseEnd_5221877 < baseStart_5221877 := by decide
  rcases family_descends (prefixWord ++ tailWord_5221877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5221963 : List Nat := [1, 1, 1, 1, 3, 1, 3, 3, 3, 2, 4]
def baseStart_5221963 : Nat := 118140960795 + 5221963 * 2 ^ 59
def prefixEnd_5221963 : Nat := 4983230072969 + 3 ^ 40 * 5221963 * 2
def baseEnd_5221963 : Nat := 2681376978994457779447135

theorem tailTrace_5221963 : CollatzResearch.WordTrace tailWord_5221963 prefixEnd_5221963 2681376978994457779447135 := by
  unfold tailWord_5221963
  simp only [CollatzResearch.WordTrace]
  refine ⟨190460637580727366122478543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126973758387151577414985695 190460637580727366122478543)
  ·
    refine ⟨285690956371091049183717815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190460637580727366122478543 285690956371091049183717815)
    ·
      refine ⟨428536434556636573775576723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285690956371091049183717815 428536434556636573775576723)
      ·
        refine ⟨642804651834954860663365085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 428536434556636573775576723 642804651834954860663365085)
        ·
          refine ⟨241051744438108072748761907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 642804651834954860663365085 241051744438108072748761907)
          ·
            refine ⟨361577616657162109123142861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241051744438108072748761907 361577616657162109123142861)
            ·
              refine ⟨135591606246435790921178573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 361577616657162109123142861 135591606246435790921178573)
              ·
                refine ⟨50846852342413421595441965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 135591606246435790921178573 50846852342413421595441965)
                ·
                  refine ⟨19067569628405033098290737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50846852342413421595441965 19067569628405033098290737)
                  ·
                    refine ⟨14300677221303774823718053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19067569628405033098290737 14300677221303774823718053)
                    ·
                      refine ⟨2681376978994457779447135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14300677221303774823718053 2681376978994457779447135)
                      ·
                        rfl

theorem cell23_5221963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 3, 2, 4].length) (baseStart_5221963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5221963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5221963 prefixEnd_5221963 := by exact prefixLift 5221963
  have htrace : WordTrace (prefixWord ++ tailWord_5221963) baseStart_5221963 baseEnd_5221963 := by
    simpa [prefixWord, tailWord_5221963, baseEnd_5221963] using wordTrace_append hprefix tailTrace_5221963
  have hstable : (prefixWord ++ tailWord_5221963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5221963).length < 2 ^ (prefixWord ++ tailWord_5221963).sum := by decide
  have hdescent : baseEnd_5221963 < baseStart_5221963 := by decide
  rcases family_descends (prefixWord ++ tailWord_5221963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5221970 : List Nat := [3, 2, 2, 1, 2, 2, 1, 3, 1, 1, 5]
def baseStart_5221970 : Nat := 118140960795 + 5221970 * 2 ^ 59
def prefixEnd_5221970 : Nat := 4983230072969 + 3 ^ 40 * 5221970 * 2
def baseEnd_5221970 : Nat := 2681380573359039252059603

theorem tailTrace_5221970 : CollatzResearch.WordTrace tailWord_5221970 prefixEnd_5221970 2681380573359039252059603 := by
  unfold tailWord_5221970
  simp only [CollatzResearch.WordTrace]
  refine ⟨47615223222925501579495841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126973928594468004211988909 47615223222925501579495841)
  ·
    refine ⟨35711417417194126184621881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47615223222925501579495841 35711417417194126184621881)
    ·
      refine ⟨26783563062895594638466411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35711417417194126184621881 26783563062895594638466411)
      ·
        refine ⟨40175344594343391957699617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26783563062895594638466411 40175344594343391957699617)
        ·
          refine ⟨30131508445757543968274713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40175344594343391957699617 30131508445757543968274713)
          ·
            refine ⟨22598631334318157976206035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30131508445757543968274713 22598631334318157976206035)
            ·
              refine ⟨33897947001477236964309053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22598631334318157976206035 33897947001477236964309053)
              ·
                refine ⟨12711730125553963861615895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33897947001477236964309053 12711730125553963861615895)
                ·
                  refine ⟨19067595188330945792423843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12711730125553963861615895 19067595188330945792423843)
                  ·
                    refine ⟨28601392782496418688635765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19067595188330945792423843 28601392782496418688635765)
                    ·
                      refine ⟨2681380573359039252059603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28601392782496418688635765 2681380573359039252059603)
                      ·
                        rfl

theorem cell23_5221970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_5221970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5221970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5221970 prefixEnd_5221970 := by exact prefixLift 5221970
  have htrace : WordTrace (prefixWord ++ tailWord_5221970) baseStart_5221970 baseEnd_5221970 := by
    simpa [prefixWord, tailWord_5221970, baseEnd_5221970] using wordTrace_append hprefix tailTrace_5221970
  have hstable : (prefixWord ++ tailWord_5221970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5221970).length < 2 ^ (prefixWord ++ tailWord_5221970).sum := by decide
  have hdescent : baseEnd_5221970 < baseStart_5221970 := by decide
  rcases family_descends (prefixWord ++ tailWord_5221970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5221980 : List Nat := [2, 2, 4, 1, 2, 1, 1, 2, 1, 1, 6]
def baseStart_5221980 : Nat := 118140960795 + 5221980 * 2 ^ 59
def prefixEnd_5221980 : Nat := 4983230072969 + 3 ^ 40 * 5221980 * 2
def baseEnd_5221980 : Nat := 2681385708165584212934557

theorem tailTrace_5221980 : CollatzResearch.WordTrace tailWord_5221980 prefixEnd_5221980 2681385708165584212934557 := by
  unfold tailWord_5221980
  simp only [CollatzResearch.WordTrace]
  refine ⟨95230628810832889012923697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126974171747777185350564929 95230628810832889012923697)
  ·
    refine ⟨71422971608124666759692773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95230628810832889012923697 71422971608124666759692773)
    ·
      refine ⟨13391807176523375017442395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71422971608124666759692773 13391807176523375017442395)
      ·
        refine ⟨20087710764785062526163593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13391807176523375017442395 20087710764785062526163593)
        ·
          refine ⟨15065783073588796894622695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20087710764785062526163593 15065783073588796894622695)
          ·
            refine ⟨22598674610383195341934043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15065783073588796894622695 22598674610383195341934043)
            ·
              refine ⟨33898011915574793012901065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22598674610383195341934043 33898011915574793012901065)
              ·
                refine ⟨25423508936681094759675799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33898011915574793012901065 25423508936681094759675799)
                ·
                  refine ⟨38135263405021642139513699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25423508936681094759675799 38135263405021642139513699)
                  ·
                    refine ⟨57202895107532463209270549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38135263405021642139513699 57202895107532463209270549)
                    ·
                      refine ⟨2681385708165584212934557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57202895107532463209270549 2681385708165584212934557)
                      ·
                        rfl

theorem cell23_5221980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_5221980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5221980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5221980 prefixEnd_5221980 := by exact prefixLift 5221980
  have htrace : WordTrace (prefixWord ++ tailWord_5221980) baseStart_5221980 baseEnd_5221980 := by
    simpa [prefixWord, tailWord_5221980, baseEnd_5221980] using wordTrace_append hprefix tailTrace_5221980
  have hstable : (prefixWord ++ tailWord_5221980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5221980).length < 2 ^ (prefixWord ++ tailWord_5221980).sum := by decide
  have hdescent : baseEnd_5221980 < baseStart_5221980 := by decide
  rcases family_descends (prefixWord ++ tailWord_5221980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5221994 : List Nat := [3, 1, 3, 2, 1, 2, 4, 1, 2, 4]
def baseStart_5221994 : Nat := 118140960795 + 5221994 * 2 ^ 59
def prefixEnd_5221994 : Nat := 4983230072969 + 3 ^ 40 * 5221994 * 2
def baseEnd_5221994 : Nat := 893797632298249052719831

theorem tailTrace_5221994 : CollatzResearch.WordTrace tailWord_5221994 prefixEnd_5221994 893797632298249052719831 := by
  unfold tailWord_5221994
  simp only [CollatzResearch.WordTrace]
  refine ⟨47615442060903764604214259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126974512162410038944571357 47615442060903764604214259)
  ·
    refine ⟨71423163091355646906321389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47615442060903764604214259 71423163091355646906321389)
    ·
      refine ⟨26783686159258367589870521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71423163091355646906321389 26783686159258367589870521)
      ·
        refine ⟨20087764619443775692402891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26783686159258367589870521 20087764619443775692402891)
        ·
          refine ⟨30131646929165663538604337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20087764619443775692402891 30131646929165663538604337)
          ·
            refine ⟨22598735196874247653953253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30131646929165663538604337 22598735196874247653953253)
            ·
              refine ⟨4237262849413921435116235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22598735196874247653953253 4237262849413921435116235)
              ·
                refine ⟨6355894274120882152674353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4237262849413921435116235 6355894274120882152674353)
                ·
                  refine ⟨4766920705590661614505765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6355894274120882152674353 4766920705590661614505765)
                  ·
                    refine ⟨893797632298249052719831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4766920705590661614505765 893797632298249052719831)
                    ·
                      rfl

theorem cell23_5221994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 4, 1, 2, 4].length) (baseStart_5221994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5221994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5221994 prefixEnd_5221994 := by exact prefixLift 5221994
  have htrace : WordTrace (prefixWord ++ tailWord_5221994) baseStart_5221994 baseEnd_5221994 := by
    simpa [prefixWord, tailWord_5221994, baseEnd_5221994] using wordTrace_append hprefix tailTrace_5221994
  have hstable : (prefixWord ++ tailWord_5221994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5221994).length < 2 ^ (prefixWord ++ tailWord_5221994).sum := by decide
  have hdescent : baseEnd_5221994 < baseStart_5221994 := by decide
  rcases family_descends (prefixWord ++ tailWord_5221994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5222017 : List Nat := [1, 2, 4, 2, 1, 3, 1, 2, 1, 3, 3]
def baseStart_5222017 : Nat := 118140960795 + 5222017 * 2 ^ 59
def prefixEnd_5222017 : Nat := 4983230072969 + 3 ^ 40 * 5222017 * 2
def baseEnd_5222017 : Nat := 2681404706949800568171887

theorem tailTrace_5222017 : CollatzResearch.WordTrace tailWord_5222017 prefixEnd_5222017 2681404706949800568171887 := by
  unfold tailWord_5222017
  simp only [CollatzResearch.WordTrace]
  refine ⟨190462607122531733344944305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126975071415021155563296203 190462607122531733344944305)
  ·
    refine ⟨142846955341898800008708229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190462607122531733344944305 142846955341898800008708229)
    ·
      refine ⟨26783804126606025001632793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 142846955341898800008708229 26783804126606025001632793)
      ·
        refine ⟨20087853094954518751224595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26783804126606025001632793 20087853094954518751224595)
        ·
          refine ⟨30131779642431778126836893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20087853094954518751224595 30131779642431778126836893)
          ·
            refine ⟨11299417365911916797563835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30131779642431778126836893 11299417365911916797563835)
            ·
              refine ⟨16949126048867875196345753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11299417365911916797563835 16949126048867875196345753)
              ·
                refine ⟨12711844536650906397259315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16949126048867875196345753 12711844536650906397259315)
                ·
                  refine ⟨19067766804976359595888973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12711844536650906397259315 19067766804976359595888973)
                  ·
                    refine ⟨7150412551866134848458365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19067766804976359595888973 7150412551866134848458365)
                    ·
                      refine ⟨2681404706949800568171887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7150412551866134848458365 2681404706949800568171887)
                      ·
                        rfl

theorem cell23_5222017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_5222017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5222017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5222017 prefixEnd_5222017 := by exact prefixLift 5222017
  have htrace : WordTrace (prefixWord ++ tailWord_5222017) baseStart_5222017 baseEnd_5222017 := by
    simpa [prefixWord, tailWord_5222017, baseEnd_5222017] using wordTrace_append hprefix tailTrace_5222017
  have hstable : (prefixWord ++ tailWord_5222017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5222017).length < 2 ^ (prefixWord ++ tailWord_5222017).sum := by decide
  have hdescent : baseEnd_5222017 < baseStart_5222017 := by decide
  rcases family_descends (prefixWord ++ tailWord_5222017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5222040 : List Nat := [2, 1, 2, 4, 1, 2, 1, 1, 2, 3, 4]
def baseStart_5222040 : Nat := 118140960795 + 5222040 * 2 ^ 59
def prefixEnd_5222040 : Nat := 4983230072969 + 3 ^ 40 * 5222040 * 2
def baseEnd_5222040 : Nat := 2681416517004853978184281

theorem tailTrace_5222040 : CollatzResearch.WordTrace tailWord_5222040 prefixEnd_5222040 2681416517004853978184281 := by
  unfold tailWord_5222040
  simp only [CollatzResearch.WordTrace]
  refine ⟨95231723000724204136515787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126975630667632272182021049 95231723000724204136515787)
  ·
    refine ⟨142847584501086306204773681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95231723000724204136515787 142847584501086306204773681)
    ·
      refine ⟨107135688375814729653580261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142847584501086306204773681 107135688375814729653580261)
      ·
        refine ⟨20087941570465261810046299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107135688375814729653580261 20087941570465261810046299)
        ·
          refine ⟨30131912355697892715069449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20087941570465261810046299 30131912355697892715069449)
          ·
            refine ⟨22598934266773419536302087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30131912355697892715069449 22598934266773419536302087)
            ·
              refine ⟨33898401400160129304453131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22598934266773419536302087 33898401400160129304453131)
              ·
                refine ⟨50847602100240193956679697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33898401400160129304453131 50847602100240193956679697)
                ·
                  refine ⟨38135701575180145467509773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50847602100240193956679697 38135701575180145467509773)
                  ·
                    refine ⟨14300888090692554550316165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38135701575180145467509773 14300888090692554550316165)
                    ·
                      refine ⟨2681416517004853978184281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14300888090692554550316165 2681416517004853978184281)
                      ·
                        rfl

theorem cell23_5222040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_5222040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5222040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5222040 prefixEnd_5222040 := by exact prefixLift 5222040
  have htrace : WordTrace (prefixWord ++ tailWord_5222040) baseStart_5222040 baseEnd_5222040 := by
    simpa [prefixWord, tailWord_5222040, baseEnd_5222040] using wordTrace_append hprefix tailTrace_5222040
  have hstable : (prefixWord ++ tailWord_5222040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5222040).length < 2 ^ (prefixWord ++ tailWord_5222040).sum := by decide
  have hdescent : baseEnd_5222040 < baseStart_5222040 := by decide
  rcases family_descends (prefixWord ++ tailWord_5222040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5222078 : List Nat := [4, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2]
def baseStart_5222078 : Nat := 118140960795 + 5222078 * 2 ^ 59
def prefixEnd_5222078 : Nat := 4983230072969 + 3 ^ 40 * 5222078 * 2
def baseEnd_5222078 : Nat := 2681436029269724829509107

theorem tailTrace_5222078 : CollatzResearch.WordTrace tailWord_5222078 prefixEnd_5222078 2681436029269724829509107 := by
  unfold tailWord_5222078
  simp only [CollatzResearch.WordTrace]
  refine ⟨23808103996913842595364361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126976554650207160508609925 23808103996913842595364361)
  ·
    refine ⟨17856077997685381946523271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23808103996913842595364361 17856077997685381946523271)
    ·
      refine ⟨26784116996528072919784907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17856077997685381946523271 26784116996528072919784907)
      ·
        refine ⟨40176175494792109379677361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26784116996528072919784907 40176175494792109379677361)
        ·
          refine ⟨30132131621094082034758021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40176175494792109379677361 30132131621094082034758021)
          ·
            refine ⟨5649774678955140381517129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30132131621094082034758021 5649774678955140381517129)
            ·
              refine ⟨4237331009216355286137847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5649774678955140381517129 4237331009216355286137847)
              ·
                refine ⟨6355996513824532929206771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4237331009216355286137847 6355996513824532929206771)
                ·
                  refine ⟨9533994770736799393810157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6355996513824532929206771 9533994770736799393810157)
                  ·
                    refine ⟨3575248039026299772678809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9533994770736799393810157 3575248039026299772678809)
                    ·
                      refine ⟨2681436029269724829509107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3575248039026299772678809 2681436029269724829509107)
                      ·
                        rfl

theorem cell23_5222078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2].length) (baseStart_5222078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5222078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5222078 prefixEnd_5222078 := by exact prefixLift 5222078
  have htrace : WordTrace (prefixWord ++ tailWord_5222078) baseStart_5222078 baseEnd_5222078 := by
    simpa [prefixWord, tailWord_5222078, baseEnd_5222078] using wordTrace_append hprefix tailTrace_5222078
  have hstable : (prefixWord ++ tailWord_5222078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5222078).length < 2 ^ (prefixWord ++ tailWord_5222078).sum := by decide
  have hdescent : baseEnd_5222078 < baseStart_5222078 := by decide
  rcases family_descends (prefixWord ++ tailWord_5222078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5222097 : List Nat := [1, 2, 2, 1, 2, 4, 2, 4, 5]
def baseStart_5222097 : Nat := 118140960795 + 5222097 * 2 ^ 59
def prefixEnd_5222097 : Nat := 4983230072969 + 3 ^ 40 * 5222097 * 2
def baseEnd_5222097 : Nat := 297938420600240028352391

theorem tailTrace_5222097 : CollatzResearch.WordTrace tailWord_5222097 prefixEnd_5222097 297938420600240028352391 := by
  unfold tailWord_5222097
  simp only [CollatzResearch.WordTrace]
  refine ⟨190465524962241907007856545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126977016641494604671904363 190465524962241907007856545)
  ·
    refine ⟨142849143721681430255892409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190465524962241907007856545 142849143721681430255892409)
    ·
      refine ⟨107136857791261072691919307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142849143721681430255892409 107136857791261072691919307)
      ·
        refine ⟨160705286686891609037878961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107136857791261072691919307 160705286686891609037878961)
        ·
          refine ⟨120528965015168706778409221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160705286686891609037878961 120528965015168706778409221)
          ·
            refine ⟨22599180940344132520951729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 120528965015168706778409221 22599180940344132520951729)
            ·
              refine ⟨16949385705258099390713797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22599180940344132520951729 16949385705258099390713797)
              ·
                refine ⟨3178009819735893635758837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16949385705258099390713797 3178009819735893635758837)
                ·
                  refine ⟨297938420600240028352391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3178009819735893635758837 297938420600240028352391)
                  ·
                    rfl

theorem cell23_5222097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 4, 5].length) (baseStart_5222097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5222097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5222097 prefixEnd_5222097 := by exact prefixLift 5222097
  have htrace : WordTrace (prefixWord ++ tailWord_5222097) baseStart_5222097 baseEnd_5222097 := by
    simpa [prefixWord, tailWord_5222097, baseEnd_5222097] using wordTrace_append hprefix tailTrace_5222097
  have hstable : (prefixWord ++ tailWord_5222097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5222097).length < 2 ^ (prefixWord ++ tailWord_5222097).sum := by decide
  have hdescent : baseEnd_5222097 < baseStart_5222097 := by decide
  rcases family_descends (prefixWord ++ tailWord_5222097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5222108 : List Nat := [2, 2, 5, 1, 2, 2, 1, 1, 1, 4, 2]
def baseStart_5222108 : Nat := 118140960795 + 5222108 * 2 ^ 59
def prefixEnd_5222108 : Nat := 4983230072969 + 3 ^ 40 * 5222108 * 2
def baseEnd_5222108 : Nat := 2681451433689359712133969

theorem tailTrace_5222108 : CollatzResearch.WordTrace tailWord_5222108 prefixEnd_5222108 2681451433689359712133969 := by
  unfold tailWord_5222108
  simp only [CollatzResearch.WordTrace]
  refine ⟨95232963082601027943253489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126977284110134703924337985 95232963082601027943253489)
  ·
    refine ⟨71424722311950770957440117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95232963082601027943253489 71424722311950770957440117)
    ·
      refine ⟨6696067716745384777260011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 71424722311950770957440117 6696067716745384777260011)
      ·
        refine ⟨10044101575118077165890017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6696067716745384777260011 10044101575118077165890017)
        ·
          refine ⟨7533076181338557874417513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10044101575118077165890017 7533076181338557874417513)
          ·
            refine ⟨5649807136003918405813135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7533076181338557874417513 5649807136003918405813135)
            ·
              refine ⟨8474710704005877608719703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5649807136003918405813135 8474710704005877608719703)
              ·
                refine ⟨12712066056008816413079555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8474710704005877608719703 12712066056008816413079555)
                ·
                  refine ⟨19068099084013224619619333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12712066056008816413079555 19068099084013224619619333)
                  ·
                    refine ⟨3575268578252479616178625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19068099084013224619619333 3575268578252479616178625)
                    ·
                      refine ⟨2681451433689359712133969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3575268578252479616178625 2681451433689359712133969)
                      ·
                        rfl

theorem cell23_5222108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_5222108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5222108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5222108 prefixEnd_5222108 := by exact prefixLift 5222108
  have htrace : WordTrace (prefixWord ++ tailWord_5222108) baseStart_5222108 baseEnd_5222108 := by
    simpa [prefixWord, tailWord_5222108, baseEnd_5222108] using wordTrace_append hprefix tailTrace_5222108
  have hstable : (prefixWord ++ tailWord_5222108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5222108).length < 2 ^ (prefixWord ++ tailWord_5222108).sum := by decide
  have hdescent : baseEnd_5222108 < baseStart_5222108 := by decide
  rcases family_descends (prefixWord ++ tailWord_5222108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5222147 : List Nat := [1, 1, 1, 3, 2, 2, 2, 1, 4, 4, 2]
def baseStart_5222147 : Nat := 118140960795 + 5222147 * 2 ^ 59
def prefixEnd_5222147 : Nat := 4983230072969 + 3 ^ 40 * 5222147 * 2
def baseEnd_5222147 : Nat := 2681471459434885059546289

theorem tailTrace_5222147 : CollatzResearch.WordTrace tailWord_5222147 prefixEnd_5222147 2681471459434885059546289 := by
  unfold tailWord_5222147
  simp only [CollatzResearch.WordTrace]
  refine ⟨190467348612060765547176695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126978232408040510364784463 190467348612060765547176695)
  ·
    refine ⟨285701022918091148320765043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190467348612060765547176695 285701022918091148320765043)
    ·
      refine ⟨428551534377136722481147565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285701022918091148320765043 428551534377136722481147565)
      ·
        refine ⟨160706825391426270930430337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 428551534377136722481147565 160706825391426270930430337)
        ·
          refine ⟨120530119043569703197822753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160706825391426270930430337 120530119043569703197822753)
          ·
            refine ⟨90397589282677277398367065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120530119043569703197822753 90397589282677277398367065)
            ·
              refine ⟨67798191962007958048775299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90397589282677277398367065 67798191962007958048775299)
              ·
                refine ⟨101697287943011937073162949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67798191962007958048775299 101697287943011937073162949)
                ·
                  refine ⟨19068241489314738201218053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 101697287943011937073162949 19068241489314738201218053)
                  ·
                    refine ⟨3575295279246513412728385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19068241489314738201218053 3575295279246513412728385)
                    ·
                      refine ⟨2681471459434885059546289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3575295279246513412728385 2681471459434885059546289)
                      ·
                        rfl

theorem cell23_5222147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 4, 4, 2].length) (baseStart_5222147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5222147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5222147 prefixEnd_5222147 := by exact prefixLift 5222147
  have htrace : WordTrace (prefixWord ++ tailWord_5222147) baseStart_5222147 baseEnd_5222147 := by
    simpa [prefixWord, tailWord_5222147, baseEnd_5222147] using wordTrace_append hprefix tailTrace_5222147
  have hstable : (prefixWord ++ tailWord_5222147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5222147).length < 2 ^ (prefixWord ++ tailWord_5222147).sum := by decide
  have hdescent : baseEnd_5222147 < baseStart_5222147 := by decide
  rcases family_descends (prefixWord ++ tailWord_5222147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5222184 : List Nat := [2, 1, 5, 1, 1, 2, 1, 3, 2, 2, 3]
def baseStart_5222184 : Nat := 118140960795 + 5222184 * 2 ^ 59
def prefixEnd_5222184 : Nat := 4983230072969 + 3 ^ 40 * 5222184 * 2
def baseEnd_5222184 : Nat := 2681490458219101414783619

theorem tailTrace_5222184 : CollatzResearch.WordTrace tailWord_5222184 prefixEnd_5222184 2681490458219101414783619 := by
  unfold tailWord_5222184
  simp only [CollatzResearch.WordTrace]
  refine ⟨95234349056463360433136803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126979132075284480577515737 95234349056463360433136803)
  ·
    refine ⟨142851523584695040649705205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95234349056463360433136803 142851523584695040649705205)
    ·
      refine ⟨13392330336065160060909863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 142851523584695040649705205 13392330336065160060909863)
      ·
        refine ⟨20088495504097740091364795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13392330336065160060909863 20088495504097740091364795)
        ·
          refine ⟨30132743256146610137047193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20088495504097740091364795 30132743256146610137047193)
          ·
            refine ⟨22599557442109957602785395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30132743256146610137047193 22599557442109957602785395)
            ·
              refine ⟨33899336163164936404178093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22599557442109957602785395 33899336163164936404178093)
              ·
                refine ⟨12712251061186851151566785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33899336163164936404178093 12712251061186851151566785)
                ·
                  refine ⟨9534188295890138363675089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12712251061186851151566785 9534188295890138363675089)
                  ·
                    refine ⟨7150641221917603772756317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9534188295890138363675089 7150641221917603772756317)
                    ·
                      refine ⟨2681490458219101414783619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7150641221917603772756317 2681490458219101414783619)
                      ·
                        rfl

theorem cell23_5222184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_5222184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5222184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5222184 prefixEnd_5222184 := by exact prefixLift 5222184
  have htrace : WordTrace (prefixWord ++ tailWord_5222184) baseStart_5222184 baseEnd_5222184 := by
    simpa [prefixWord, tailWord_5222184, baseEnd_5222184] using wordTrace_append hprefix tailTrace_5222184
  have hstable : (prefixWord ++ tailWord_5222184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5222184).length < 2 ^ (prefixWord ++ tailWord_5222184).sum := by decide
  have hdescent : baseEnd_5222184 < baseStart_5222184 := by decide
  rcases family_descends (prefixWord ++ tailWord_5222184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5222231 : List Nat := [1, 1, 3, 2, 5, 1, 1, 2, 3, 1, 3]
def baseStart_5222231 : Nat := 118140960795 + 5222231 * 2 ^ 59
def prefixEnd_5222231 : Nat := 4983230072969 + 3 ^ 40 * 5222231 * 2
def baseEnd_5222231 : Nat := 2681514591809862730895903

theorem tailTrace_5222231 : CollatzResearch.WordTrace tailWord_5222231 prefixEnd_5222231 2681514591809862730895903 := by
  unfold tailWord_5222231
  simp only [CollatzResearch.WordTrace]
  refine ⟨190470412343756447893234547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126980274895837631928823031 190470412343756447893234547)
  ·
    refine ⟨285705618515634671839851821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190470412343756447893234547 285705618515634671839851821)
    ·
      refine ⟨107139606943363001939944433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 285705618515634671839851821 107139606943363001939944433)
      ·
        refine ⟨80354705207522251454958325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107139606943363001939944433 80354705207522251454958325)
        ·
          refine ⟨7533253613205211073902343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 80354705207522251454958325 7533253613205211073902343)
          ·
            refine ⟨11299880419807816610853515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7533253613205211073902343 11299880419807816610853515)
            ·
              refine ⟨16949820629711724916280273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11299880419807816610853515 16949820629711724916280273)
              ·
                refine ⟨12712365472283793687210205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16949820629711724916280273 12712365472283793687210205)
                ·
                  refine ⟨4767137052106422632703827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12712365472283793687210205 4767137052106422632703827)
                  ·
                    refine ⟨7150705578159633949055741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4767137052106422632703827 7150705578159633949055741)
                    ·
                      refine ⟨2681514591809862730895903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7150705578159633949055741 2681514591809862730895903)
                      ·
                        rfl

theorem cell23_5222231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 2, 3, 1, 3].length) (baseStart_5222231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5222231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5222231 prefixEnd_5222231 := by exact prefixLift 5222231
  have htrace : WordTrace (prefixWord ++ tailWord_5222231) baseStart_5222231 baseEnd_5222231 := by
    simpa [prefixWord, tailWord_5222231, baseEnd_5222231] using wordTrace_append hprefix tailTrace_5222231
  have hstable : (prefixWord ++ tailWord_5222231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5222231).length < 2 ^ (prefixWord ++ tailWord_5222231).sum := by decide
  have hdescent : baseEnd_5222231 < baseStart_5222231 := by decide
  rcases family_descends (prefixWord ++ tailWord_5222231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5222247 : List Nat := [1, 1, 5, 1, 2, 1, 1, 4, 1, 6]
def baseStart_5222247 : Nat := 118140960795 + 5222247 * 2 ^ 59
def prefixEnd_5222247 : Nat := 4983230072969 + 3 ^ 40 * 5222247 * 2
def baseEnd_5222247 : Nat := 893840935833444889431943

theorem tailTrace_5222247 : CollatzResearch.WordTrace tailWord_5222247 prefixEnd_5222247 893840935833444889431943 := by
  unfold tailWord_5222247
  simp only [CollatzResearch.WordTrace]
  refine ⟨190470995911698482625816995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126980663941132321750544663 190470995911698482625816995)
  ·
    refine ⟨285706493867547723938725493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190470995911698482625816995 285706493867547723938725493)
    ·
      refine ⟨26784983800082599119255515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 285706493867547723938725493 26784983800082599119255515)
      ·
        refine ⟨40177475700123898678883273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26784983800082599119255515 40177475700123898678883273)
        ·
          refine ⟨30133106775092924009162455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40177475700123898678883273 30133106775092924009162455)
          ·
            refine ⟨45199660162639386013743683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30133106775092924009162455 45199660162639386013743683)
            ·
              refine ⟨67799490243959079020615525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45199660162639386013743683 67799490243959079020615525)
              ·
                refine ⟨12712404420742327316365411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67799490243959079020615525 12712404420742327316365411)
                ·
                  refine ⟨19068606631113490974548117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12712404420742327316365411 19068606631113490974548117)
                  ·
                    refine ⟨893840935833444889431943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19068606631113490974548117 893840935833444889431943)
                    ·
                      rfl

theorem cell23_5222247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_5222247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5222247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5222247 prefixEnd_5222247 := by exact prefixLift 5222247
  have htrace : WordTrace (prefixWord ++ tailWord_5222247) baseStart_5222247 baseEnd_5222247 := by
    simpa [prefixWord, tailWord_5222247, baseEnd_5222247] using wordTrace_append hprefix tailTrace_5222247
  have hstable : (prefixWord ++ tailWord_5222247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5222247).length < 2 ^ (prefixWord ++ tailWord_5222247).sum := by decide
  have hdescent : baseEnd_5222247 < baseStart_5222247 := by decide
  rcases family_descends (prefixWord ++ tailWord_5222247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5222248 : List Nat := [2, 1, 4, 2, 1, 1, 4, 3, 1, 1, 3]
def baseStart_5222248 : Nat := 118140960795 + 5222248 * 2 ^ 59
def prefixEnd_5222248 : Nat := 4983230072969 + 3 ^ 40 * 5222248 * 2
def baseEnd_5222248 : Nat := 2681523320980989164383325

theorem tailTrace_5222248 : CollatzResearch.WordTrace tailWord_5222248 prefixEnd_5222248 2681523320980989164383325 := by
  unfold tailWord_5222248
  simp only [CollatzResearch.WordTrace]
  refine ⟨95235516192347429898301699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126980688256463239864402265 95235516192347429898301699)
  ·
    refine ⟨142853274288521144847452549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95235516192347429898301699 142853274288521144847452549)
    ·
      refine ⟨26784988929097714658897353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 142853274288521144847452549 26784988929097714658897353)
      ·
        refine ⟨20088741696823285994173015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26784988929097714658897353 20088741696823285994173015)
        ·
          refine ⟨30133112545234928991259523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20088741696823285994173015 30133112545234928991259523)
          ·
            refine ⟨45199668817852393486889285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30133112545234928991259523 45199668817852393486889285)
            ·
              refine ⟨8474937903347323778791741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45199668817852393486889285 8474937903347323778791741)
              ·
                refine ⟨3178101713755246417046903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8474937903347323778791741 3178101713755246417046903)
                ·
                  refine ⟨4767152570632869625570355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3178101713755246417046903 4767152570632869625570355)
                  ·
                    refine ⟨7150728855949304438355533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4767152570632869625570355 7150728855949304438355533)
                    ·
                      refine ⟨2681523320980989164383325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7150728855949304438355533 2681523320980989164383325)
                      ·
                        rfl

theorem cell23_5222248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 3, 1, 1, 3].length) (baseStart_5222248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5222248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5222248 prefixEnd_5222248 := by exact prefixLift 5222248
  have htrace : WordTrace (prefixWord ++ tailWord_5222248) baseStart_5222248 baseEnd_5222248 := by
    simpa [prefixWord, tailWord_5222248, baseEnd_5222248] using wordTrace_append hprefix tailTrace_5222248
  have hstable : (prefixWord ++ tailWord_5222248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5222248).length < 2 ^ (prefixWord ++ tailWord_5222248).sum := by decide
  have hdescent : baseEnd_5222248 < baseStart_5222248 := by decide
  rcases family_descends (prefixWord ++ tailWord_5222248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5222257 : List Nat := [1, 2, 2, 2, 1, 3, 2, 3, 1, 1, 5]
def baseStart_5222257 : Nat := 118140960795 + 5222257 * 2 ^ 59
def prefixEnd_5222257 : Nat := 4983230072969 + 3 ^ 40 * 5222257 * 2
def baseEnd_5222257 : Nat := 2681527942306879629170783

theorem tailTrace_5222257 : CollatzResearch.WordTrace tailWord_5222257 prefixEnd_5222257 2681527942306879629170783 := by
  unfold tailWord_5222257
  simp only [CollatzResearch.WordTrace]
  refine ⟨190471360641662254333681025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126980907094441502889120683 190471360641662254333681025)
  ·
    refine ⟨142853520481246690750260769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190471360641662254333681025 142853520481246690750260769)
    ·
      refine ⟨107140140360935018062695577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142853520481246690750260769 107140140360935018062695577)
      ·
        refine ⟨80355105270701263547021683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107140140360935018062695577 80355105270701263547021683)
        ·
          refine ⟨120532657906051895320532525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80355105270701263547021683 120532657906051895320532525)
          ·
            refine ⟨45199746714769460745199697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120532657906051895320532525 45199746714769460745199697)
            ·
              refine ⟨33899810036077095558899773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45199746714769460745199697 33899810036077095558899773)
              ·
                refine ⟨12712428763528910834587415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33899810036077095558899773 12712428763528910834587415)
                ·
                  refine ⟨19068643145293366251881123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12712428763528910834587415 19068643145293366251881123)
                  ·
                    refine ⟨28602964717940049377821685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19068643145293366251881123 28602964717940049377821685)
                    ·
                      refine ⟨2681527942306879629170783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28602964717940049377821685 2681527942306879629170783)
                      ·
                        rfl

theorem cell23_5222257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 3, 1, 1, 5].length) (baseStart_5222257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5222257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5222257 prefixEnd_5222257 := by exact prefixLift 5222257
  have htrace : WordTrace (prefixWord ++ tailWord_5222257) baseStart_5222257 baseEnd_5222257 := by
    simpa [prefixWord, tailWord_5222257, baseEnd_5222257] using wordTrace_append hprefix tailTrace_5222257
  have hstable : (prefixWord ++ tailWord_5222257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5222257).length < 2 ^ (prefixWord ++ tailWord_5222257).sum := by decide
  have hdescent : baseEnd_5222257 < baseStart_5222257 := by decide
  rcases family_descends (prefixWord ++ tailWord_5222257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5222281 : List Nat := [1, 2, 1, 1, 5, 1, 5, 1, 2, 4]
def baseStart_5222281 : Nat := 118140960795 + 5222281 * 2 ^ 59
def prefixEnd_5222281 : Nat := 4983230072969 + 3 ^ 40 * 5222281 * 2
def baseEnd_5222281 : Nat := 893846755280862511756891

theorem tailTrace_5222281 : CollatzResearch.WordTrace tailWord_5222281 prefixEnd_5222281 893846755280862511756891 := by
  unfold tailWord_5222281
  simp only [CollatzResearch.WordTrace]
  refine ⟨190472235993575306432554697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126981490662383537621703131 190472235993575306432554697)
  ·
    refine ⟨142854176995181479824416023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190472235993575306432554697 142854176995181479824416023)
    ·
      refine ⟨214281265492772219736624035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142854176995181479824416023 214281265492772219736624035)
      ·
        refine ⟨321421898239158329604936053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214281265492772219736624035 321421898239158329604936053)
        ·
          refine ⟨30133302959921093400462755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 321421898239158329604936053 30133302959921093400462755)
          ·
            refine ⟨45199954439881640100694133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30133302959921093400462755 45199954439881640100694133)
            ·
              refine ⟨4237495728738903759440075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45199954439881640100694133 4237495728738903759440075)
              ·
                refine ⟨6356243593108355639160113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4237495728738903759440075 6356243593108355639160113)
                ·
                  refine ⟨4767182694831266729370085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6356243593108355639160113 4767182694831266729370085)
                  ·
                    refine ⟨893846755280862511756891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4767182694831266729370085 893846755280862511756891)
                    ·
                      rfl

theorem cell23_5222281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 5, 1, 2, 4].length) (baseStart_5222281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5222281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5222281 prefixEnd_5222281 := by exact prefixLift 5222281
  have htrace : WordTrace (prefixWord ++ tailWord_5222281) baseStart_5222281 baseEnd_5222281 := by
    simpa [prefixWord, tailWord_5222281, baseEnd_5222281] using wordTrace_append hprefix tailTrace_5222281
  have hstable : (prefixWord ++ tailWord_5222281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5222281).length < 2 ^ (prefixWord ++ tailWord_5222281).sum := by decide
  have hdescent : baseEnd_5222281 < baseStart_5222281 := by decide
  rcases family_descends (prefixWord ++ tailWord_5222281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5222321 : List Nat := [1, 2, 2, 4, 2, 1, 2, 1, 4, 1, 3]
def baseStart_5222321 : Nat := 118140960795 + 5222321 * 2 ^ 59
def prefixEnd_5222321 : Nat := 4983230072969 + 3 ^ 40 * 5222321 * 2
def baseEnd_5222321 : Nat := 2681560805068767378770489

theorem tailTrace_5222321 : CollatzResearch.WordTrace tailWord_5222321 prefixEnd_5222321 2681560805068767378770489 := by
  unfold tailWord_5222321
  simp only [CollatzResearch.WordTrace]
  refine ⟨190473694913430393264010817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126982463275620262176007211 190473694913430393264010817)
  ·
    refine ⟨142855271185072794948008113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190473694913430393264010817 142855271185072794948008113)
    ·
      refine ⟨107141453388804596211006085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142855271185072794948008113 107141453388804596211006085)
      ·
        refine ⟨20089022510400861789563641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107141453388804596211006085 20089022510400861789563641)
        ·
          refine ⟨15066766882800646342172731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20089022510400861789563641 15066766882800646342172731)
          ·
            refine ⟨22600150324200969513259097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15066766882800646342172731 22600150324200969513259097)
            ·
              refine ⟨16950112743150727134944323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22600150324200969513259097 16950112743150727134944323)
              ·
                refine ⟨25425169114726090702416485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16950112743150727134944323 25425169114726090702416485)
                ·
                  refine ⟨4767219209011142006703091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25425169114726090702416485 4767219209011142006703091)
                  ·
                    refine ⟨7150828813516713010054637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4767219209011142006703091 7150828813516713010054637)
                    ·
                      refine ⟨2681560805068767378770489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7150828813516713010054637 2681560805068767378770489)
                      ·
                        rfl

theorem cell23_5222321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_5222321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5222321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5222321 prefixEnd_5222321 := by exact prefixLift 5222321
  have htrace : WordTrace (prefixWord ++ tailWord_5222321) baseStart_5222321 baseEnd_5222321 := by
    simpa [prefixWord, tailWord_5222321, baseEnd_5222321] using wordTrace_append hprefix tailTrace_5222321
  have hstable : (prefixWord ++ tailWord_5222321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5222321).length < 2 ^ (prefixWord ++ tailWord_5222321).sum := by decide
  have hdescent : baseEnd_5222321 < baseStart_5222321 := by decide
  rcases family_descends (prefixWord ++ tailWord_5222321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5222327 : List Nat := [1, 1, 3, 1, 3, 1, 1, 3, 2, 3, 4]
def baseStart_5222327 : Nat := 118140960795 + 5222327 * 2 ^ 59
def prefixEnd_5222327 : Nat := 4983230072969 + 3 ^ 40 * 5222327 * 2
def baseEnd_5222327 : Nat := 2681563885952694355295461

theorem tailTrace_5222327 : CollatzResearch.WordTrace tailWord_5222327 prefixEnd_5222327 2681563885952694355295461 := by
  unfold tailWord_5222327
  simp only [CollatzResearch.WordTrace]
  refine ⟨190473913751408656288729235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126982609167605770859152823 190473913751408656288729235)
  ·
    refine ⟨285710870627112984433093853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190473913751408656288729235 285710870627112984433093853)
    ·
      refine ⟨107141576485167369162410195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 285710870627112984433093853 107141576485167369162410195)
      ·
        refine ⟨160712364727751053743615293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107141576485167369162410195 160712364727751053743615293)
        ·
          refine ⟨60267136772906645153855735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 160712364727751053743615293 60267136772906645153855735)
          ·
            refine ⟨90400705159359967730783603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60267136772906645153855735 90400705159359967730783603)
            ·
              refine ⟨135601057739039951596175405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90400705159359967730783603 135601057739039951596175405)
              ·
                refine ⟨50850396652139981848565777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 135601057739039951596175405 50850396652139981848565777)
                ·
                  refine ⟨38137797489104986386424333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50850396652139981848565777 38137797489104986386424333)
                  ·
                    refine ⟨14301674058414369894909125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38137797489104986386424333 14301674058414369894909125)
                    ·
                      refine ⟨2681563885952694355295461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14301674058414369894909125 2681563885952694355295461)
                      ·
                        rfl

theorem cell23_5222327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 3, 4].length) (baseStart_5222327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5222327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5222327 prefixEnd_5222327 := by exact prefixLift 5222327
  have htrace : WordTrace (prefixWord ++ tailWord_5222327) baseStart_5222327 baseEnd_5222327 := by
    simpa [prefixWord, tailWord_5222327, baseEnd_5222327] using wordTrace_append hprefix tailTrace_5222327
  have hstable : (prefixWord ++ tailWord_5222327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5222327).length < 2 ^ (prefixWord ++ tailWord_5222327).sum := by decide
  have hdescent : baseEnd_5222327 < baseStart_5222327 := by decide
  rcases family_descends (prefixWord ++ tailWord_5222327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5222332 : List Nat := [2, 2, 2, 5, 2, 1, 2, 1, 2, 4]
def baseStart_5222332 : Nat := 118140960795 + 5222332 * 2 ^ 59
def prefixEnd_5222332 : Nat := 4983230072969 + 3 ^ 40 * 5222332 * 2
def baseEnd_5222332 : Nat := 893855484451988945244313

theorem tailTrace_5222332 : CollatzResearch.WordTrace tailWord_5222332 prefixEnd_5222332 893855484451988945244313 := by
  unfold tailWord_5222332
  simp only [CollatzResearch.WordTrace]
  refine ⟨95237048058195271071330625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126982730744260361428440833 95237048058195271071330625)
  ·
    refine ⟨71427786043646453303497969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95237048058195271071330625 71427786043646453303497969)
    ·
      refine ⟨53570839532734839977623477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71427786043646453303497969 53570839532734839977623477)
      ·
        refine ⟨5022266206193891247902201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53570839532734839977623477 5022266206193891247902201)
        ·
          refine ⟨3766699654645418435926651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5022266206193891247902201 3766699654645418435926651)
          ·
            refine ⟨5650049481968127653889977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3766699654645418435926651 5650049481968127653889977)
            ·
              refine ⟨4237537111476095740417483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5650049481968127653889977 4237537111476095740417483)
              ·
                refine ⟨6356305667214143610626225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4237537111476095740417483 6356305667214143610626225)
                ·
                  refine ⟨4767229250410607707969669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6356305667214143610626225 4767229250410607707969669)
                  ·
                    refine ⟨893855484451988945244313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4767229250410607707969669 893855484451988945244313)
                    ·
                      rfl

theorem cell23_5222332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 2, 1, 2, 4].length) (baseStart_5222332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5222332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5222332 prefixEnd_5222332 := by exact prefixLift 5222332
  have htrace : WordTrace (prefixWord ++ tailWord_5222332) baseStart_5222332 baseEnd_5222332 := by
    simpa [prefixWord, tailWord_5222332, baseEnd_5222332] using wordTrace_append hprefix tailTrace_5222332
  have hstable : (prefixWord ++ tailWord_5222332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5222332).length < 2 ^ (prefixWord ++ tailWord_5222332).sum := by decide
  have hdescent : baseEnd_5222332 < baseStart_5222332 := by decide
  rcases family_descends (prefixWord ++ tailWord_5222332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5222347 : List Nat := [1, 1, 1, 1, 3, 4, 1, 1, 4, 1, 5]
def baseStart_5222347 : Nat := 118140960795 + 5222347 * 2 ^ 59
def prefixEnd_5222347 : Nat := 4983230072969 + 3 ^ 40 * 5222347 * 2
def baseEnd_5222347 : Nat := 2681574155565784277045369

theorem tailTrace_5222347 : CollatzResearch.WordTrace tailWord_5222347 prefixEnd_5222347 2681574155565784277045369 := by
  unfold tailWord_5222347
  simp only [CollatzResearch.WordTrace]
  refine ⟨190474643211336199704457295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126983095474224133136304863 190474643211336199704457295)
  ·
    refine ⟨285711964817004299556685943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190474643211336199704457295 285711964817004299556685943)
    ·
      refine ⟨428567947225506449335028915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285711964817004299556685943 428567947225506449335028915)
      ·
        refine ⟨642851920838259674002543373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 428567947225506449335028915 642851920838259674002543373)
        ·
          refine ⟨241069470314347377750953765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 642851920838259674002543373 241069470314347377750953765)
          ·
            refine ⟨45200525683940133328303831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 241069470314347377750953765 45200525683940133328303831)
            ·
              refine ⟨67800788525910199992455747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45200525683940133328303831 67800788525910199992455747)
              ·
                refine ⟨101701182788865299988683621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67800788525910199992455747 101701182788865299988683621)
                ·
                  refine ⟨19068971772912243747878179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 101701182788865299988683621 19068971772912243747878179)
                  ·
                    refine ⟨28603457659368365621817269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19068971772912243747878179 28603457659368365621817269)
                    ·
                      refine ⟨2681574155565784277045369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28603457659368365621817269 2681574155565784277045369)
                      ·
                        rfl

theorem cell23_5222347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 4, 1, 5].length) (baseStart_5222347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5222347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5222347 prefixEnd_5222347 := by exact prefixLift 5222347
  have htrace : WordTrace (prefixWord ++ tailWord_5222347) baseStart_5222347 baseEnd_5222347 := by
    simpa [prefixWord, tailWord_5222347, baseEnd_5222347] using wordTrace_append hprefix tailTrace_5222347
  have hstable : (prefixWord ++ tailWord_5222347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5222347).length < 2 ^ (prefixWord ++ tailWord_5222347).sum := by decide
  have hdescent : baseEnd_5222347 < baseStart_5222347 := by decide
  rcases family_descends (prefixWord ++ tailWord_5222347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5222348 : List Nat := [2, 2, 1, 4, 1, 2, 3, 2, 1, 3, 2]
def baseStart_5222348 : Nat := 118140960795 + 5222348 * 2 ^ 59
def prefixEnd_5222348 : Nat := 4983230072969 + 3 ^ 40 * 5222348 * 2
def baseEnd_5222348 : Nat := 2681574669046438773132865

theorem tailTrace_5222348 : CollatzResearch.WordTrace tailWord_5222348 prefixEnd_5222348 2681574669046438773132865 := by
  unfold tailWord_5222348
  simp only [CollatzResearch.WordTrace]
  refine ⟨95237339842166288437621849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126983119789555051250162465 95237339842166288437621849)
  ·
    refine ⟨71428004881624716328216387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95237339842166288437621849 71428004881624716328216387)
    ·
      refine ⟨107142007322437074492324581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71428004881624716328216387 107142007322437074492324581)
      ·
        refine ⟨20089126372956951467310859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107142007322437074492324581 20089126372956951467310859)
        ·
          refine ⟨30133689559435427200966289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20089126372956951467310859 30133689559435427200966289)
          ·
            refine ⟨22600267169576570400724717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30133689559435427200966289 22600267169576570400724717)
            ·
              refine ⟨8475100188591213900271769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22600267169576570400724717 8475100188591213900271769)
              ·
                refine ⟨6356325141443410425203827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8475100188591213900271769 6356325141443410425203827)
                ·
                  refine ⟨9534487712165115637805741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6356325141443410425203827 9534487712165115637805741)
                  ·
                    refine ⟨3575432892061918364177153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9534487712165115637805741 3575432892061918364177153)
                    ·
                      refine ⟨2681574669046438773132865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3575432892061918364177153 2681574669046438773132865)
                      ·
                        rfl

theorem cell23_5222348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 2, 1, 3, 2].length) (baseStart_5222348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5222348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5222348 prefixEnd_5222348 := by exact prefixLift 5222348
  have htrace : WordTrace (prefixWord ++ tailWord_5222348) baseStart_5222348 baseEnd_5222348 := by
    simpa [prefixWord, tailWord_5222348, baseEnd_5222348] using wordTrace_append hprefix tailTrace_5222348
  have hstable : (prefixWord ++ tailWord_5222348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5222348).length < 2 ^ (prefixWord ++ tailWord_5222348).sum := by decide
  have hdescent : baseEnd_5222348 < baseStart_5222348 := by decide
  rcases family_descends (prefixWord ++ tailWord_5222348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5222414 : List Nat := [4, 1, 1, 2, 2, 1, 3, 1, 1, 7]
def baseStart_5222414 : Nat := 118140960795 + 5222414 * 2 ^ 59
def prefixEnd_5222414 : Nat := 4983230072969 + 3 ^ 40 * 5222414 * 2
def baseEnd_5222414 : Nat := 893869519589878504969187

theorem tailTrace_5222414 : CollatzResearch.WordTrace tailWord_5222414 prefixEnd_5222414 893869519589878504969187 := by
  unfold tailWord_5222414
  simp only [CollatzResearch.WordTrace]
  refine ⟨23809635862761683768393287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126984724601395646764764197 23809635862761683768393287)
  ·
    refine ⟨35714453794142525652589931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23809635862761683768393287 35714453794142525652589931)
    ·
      refine ⟨53571680691213788478884897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35714453794142525652589931 53571680691213788478884897)
      ·
        refine ⟨40178760518410341359163673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53571680691213788478884897 40178760518410341359163673)
        ·
          refine ⟨30134070388807756019372755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40178760518410341359163673 30134070388807756019372755)
          ·
            refine ⟨45201105583211634029059133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30134070388807756019372755 45201105583211634029059133)
            ·
              refine ⟨16950414593704362760897175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45201105583211634029059133 16950414593704362760897175)
              ·
                refine ⟨25425621890556544141345763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16950414593704362760897175 25425621890556544141345763)
                ·
                  refine ⟨38138432835834816212018645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25425621890556544141345763 38138432835834816212018645)
                  ·
                    refine ⟨893869519589878504969187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38138432835834816212018645 893869519589878504969187)
                    ·
                      rfl

theorem cell23_5222414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 1, 7].length) (baseStart_5222414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5222414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5222414 prefixEnd_5222414 := by exact prefixLift 5222414
  have htrace : WordTrace (prefixWord ++ tailWord_5222414) baseStart_5222414 baseEnd_5222414 := by
    simpa [prefixWord, tailWord_5222414, baseEnd_5222414] using wordTrace_append hprefix tailTrace_5222414
  have hstable : (prefixWord ++ tailWord_5222414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5222414).length < 2 ^ (prefixWord ++ tailWord_5222414).sum := by decide
  have hdescent : baseEnd_5222414 < baseStart_5222414 := by decide
  rcases family_descends (prefixWord ++ tailWord_5222414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5222451 : List Nat := [1, 1, 1, 2, 4, 1, 4, 1, 2, 4, 2]
def baseStart_5222451 : Nat := 118140960795 + 5222451 * 2 ^ 59
def prefixEnd_5222451 : Nat := 4983230072969 + 3 ^ 40 * 5222451 * 2
def baseEnd_5222451 : Nat := 2681627557553851870144891

theorem tailTrace_5222451 : CollatzResearch.WordTrace tailWord_5222451 prefixEnd_5222451 2681627557553851870144891 := by
  unfold tailWord_5222451
  simp only [CollatzResearch.WordTrace]
  refine ⟨190478436402959425466243207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126985624268639616977495471 190478436402959425466243207)
  ·
    refine ⟨285717654604439138199364811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190478436402959425466243207 285717654604439138199364811)
    ·
      refine ⟨428576481906658707299047217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285717654604439138199364811 428576481906658707299047217)
      ·
        refine ⟨321432361429994030474285413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 428576481906658707299047217 321432361429994030474285413)
        ·
          refine ⟨60268567768123880713928515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 321432361429994030474285413 60268567768123880713928515)
          ·
            refine ⟨90402851652185821070892773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60268567768123880713928515 90402851652185821070892773)
            ·
              refine ⟨16950534684784841450792395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90402851652185821070892773 16950534684784841450792395)
              ·
                refine ⟨25425802027177262176188593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16950534684784841450792395 25425802027177262176188593)
                ·
                  refine ⟨19069351520382946632141445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25425802027177262176188593 19069351520382946632141445)
                  ·
                    refine ⟨3575503410071802493526521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19069351520382946632141445 3575503410071802493526521)
                    ·
                      refine ⟨2681627557553851870144891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3575503410071802493526521 2681627557553851870144891)
                      ·
                        rfl

theorem cell23_5222451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 2, 4, 2].length) (baseStart_5222451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5222451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5222451 prefixEnd_5222451 := by exact prefixLift 5222451
  have htrace : WordTrace (prefixWord ++ tailWord_5222451) baseStart_5222451 baseEnd_5222451 := by
    simpa [prefixWord, tailWord_5222451, baseEnd_5222451] using wordTrace_append hprefix tailTrace_5222451
  have hstable : (prefixWord ++ tailWord_5222451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5222451).length < 2 ^ (prefixWord ++ tailWord_5222451).sum := by decide
  have hdescent : baseEnd_5222451 < baseStart_5222451 := by decide
  rcases family_descends (prefixWord ++ tailWord_5222451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5222461 : List Nat := [1, 4, 1, 3, 1, 1, 1, 4, 3, 4]
def baseStart_5222461 : Nat := 118140960795 + 5222461 * 2 ^ 59
def prefixEnd_5222461 : Nat := 4983230072969 + 3 ^ 40 * 5222461 * 2
def baseEnd_5222461 : Nat := 893877564120132277006615

theorem tailTrace_5222461 : CollatzResearch.WordTrace tailWord_5222461 prefixEnd_5222461 893877564120132277006615 := by
  unfold tailWord_5222461
  simp only [CollatzResearch.WordTrace]
  refine ⟨190478801132923197174107237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126985867421948798116071491 190478801132923197174107237)
  ·
    refine ⟨35714775212423099470145107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 190478801132923197174107237 35714775212423099470145107)
    ·
      refine ⟨53572162818634649205217661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35714775212423099470145107 53572162818634649205217661)
      ·
        refine ⟨20089561056987993451956623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53572162818634649205217661 20089561056987993451956623)
        ·
          refine ⟨30134341585481990177934935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20089561056987993451956623 30134341585481990177934935)
          ·
            refine ⟨45201512378222985266902403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30134341585481990177934935 45201512378222985266902403)
            ·
              refine ⟨67802268567334477900353605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45201512378222985266902403 67802268567334477900353605)
              ·
                refine ⟨12712925356375214606316301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67802268567334477900353605 12712925356375214606316301)
                ·
                  refine ⟨4767347008640705477368613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12712925356375214606316301 4767347008640705477368613)
                  ·
                    refine ⟨893877564120132277006615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4767347008640705477368613 893877564120132277006615)
                    ·
                      rfl

theorem cell23_5222461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 4, 3, 4].length) (baseStart_5222461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5222461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5222461 prefixEnd_5222461 := by exact prefixLift 5222461
  have htrace : WordTrace (prefixWord ++ tailWord_5222461) baseStart_5222461 baseEnd_5222461 := by
    simpa [prefixWord, tailWord_5222461, baseEnd_5222461] using wordTrace_append hprefix tailTrace_5222461
  have hstable : (prefixWord ++ tailWord_5222461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5222461).length < 2 ^ (prefixWord ++ tailWord_5222461).sum := by decide
  have hdescent : baseEnd_5222461 < baseStart_5222461 := by decide
  rcases family_descends (prefixWord ++ tailWord_5222461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5222471 : List Nat := [1, 1, 4, 1, 3, 1, 2, 3, 2, 2, 3]
def baseStart_5222471 : Nat := 118140960795 + 5222471 * 2 ^ 59
def prefixEnd_5222471 : Nat := 4983230072969 + 3 ^ 40 * 5222471 * 2
def baseEnd_5222471 : Nat := 2681637827166941791894799

theorem tailTrace_5222471 : CollatzResearch.WordTrace tailWord_5222471 prefixEnd_5222471 2681637827166941791894799 := by
  unfold tailWord_5222471
  simp only [CollatzResearch.WordTrace]
  refine ⟨190479165862886968881971267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126986110575257979254647511 190479165862886968881971267)
  ·
    refine ⟨285718748794330453322956901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190479165862886968881971267 285718748794330453322956901)
    ·
      refine ⟨53572265398936959998054419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 285718748794330453322956901 53572265398936959998054419)
      ·
        refine ⟨80358398098405439997081629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53572265398936959998054419 80358398098405439997081629)
        ·
          refine ⟨30134399286902039998905611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80358398098405439997081629 30134399286902039998905611)
          ·
            refine ⟨45201598930353059998358417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30134399286902039998905611 45201598930353059998358417)
            ·
              refine ⟨33901199197764794998768813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45201598930353059998358417 33901199197764794998768813)
              ·
                refine ⟨12712949699161798124538305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33901199197764794998768813 12712949699161798124538305)
                ·
                  refine ⟨9534712274371348593403729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12712949699161798124538305 9534712274371348593403729)
                  ·
                    refine ⟨7151034205778511445052797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9534712274371348593403729 7151034205778511445052797)
                    ·
                      refine ⟨2681637827166941791894799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7151034205778511445052797 2681637827166941791894799)
                      ·
                        rfl

theorem cell23_5222471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 3, 2, 2, 3].length) (baseStart_5222471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5222471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5222471 prefixEnd_5222471 := by exact prefixLift 5222471
  have htrace : WordTrace (prefixWord ++ tailWord_5222471) baseStart_5222471 baseEnd_5222471 := by
    simpa [prefixWord, tailWord_5222471, baseEnd_5222471] using wordTrace_append hprefix tailTrace_5222471
  have hstable : (prefixWord ++ tailWord_5222471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5222471).length < 2 ^ (prefixWord ++ tailWord_5222471).sum := by decide
  have hdescent : baseEnd_5222471 < baseStart_5222471 := by decide
  rcases family_descends (prefixWord ++ tailWord_5222471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5222508 : List Nat := [2, 2, 1, 1, 3, 5, 2, 1, 6]
def baseStart_5222508 : Nat := 118140960795 + 5222508 * 2 ^ 59
def prefixEnd_5222508 : Nat := 4983230072969 + 3 ^ 40 * 5222508 * 2
def baseEnd_5222508 : Nat := 297961869550128683014681

theorem tailTrace_5222508 : CollatzResearch.WordTrace tailWord_5222508 prefixEnd_5222508 297961869550128683014681 := by
  unfold tailWord_5222508
  simp only [CollatzResearch.WordTrace]
  refine ⟨95240257681876462100534089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126987010242501949467378785 95240257681876462100534089)
  ·
    refine ⟨71430193261407346575400567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95240257681876462100534089 71430193261407346575400567)
    ·
      refine ⟨107145289892111019863100851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71430193261407346575400567 107145289892111019863100851)
      ·
        refine ⟨160717934838166529794651277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107145289892111019863100851 160717934838166529794651277)
        ·
          refine ⟨60269225564312448672994229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 160717934838166529794651277 60269225564312448672994229)
          ·
            refine ⟨5650239896654292063093209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60269225564312448672994229 5650239896654292063093209)
            ·
              refine ⟨4237679922490719047319907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5650239896654292063093209 4237679922490719047319907)
              ·
                refine ⟨6356519883736078570979861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4237679922490719047319907 6356519883736078570979861)
                ·
                  refine ⟨297961869550128683014681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6356519883736078570979861 297961869550128683014681)
                  ·
                    rfl

theorem cell23_5222508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 6].length) (baseStart_5222508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5222508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5222508 prefixEnd_5222508 := by exact prefixLift 5222508
  have htrace : WordTrace (prefixWord ++ tailWord_5222508) baseStart_5222508 baseEnd_5222508 := by
    simpa [prefixWord, tailWord_5222508, baseEnd_5222508] using wordTrace_append hprefix tailTrace_5222508
  have hstable : (prefixWord ++ tailWord_5222508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5222508).length < 2 ^ (prefixWord ++ tailWord_5222508).sum := by decide
  have hdescent : baseEnd_5222508 < baseStart_5222508 := by decide
  rcases family_descends (prefixWord ++ tailWord_5222508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5222521 : List Nat := [1, 2, 1, 3, 4, 2, 1, 1, 3, 5]
def baseStart_5222521 : Nat := 118140960795 + 5222521 * 2 ^ 59
def prefixEnd_5222521 : Nat := 4983230072969 + 3 ^ 40 * 5222521 * 2
def baseEnd_5222521 : Nat := 893887833733222198756523

theorem tailTrace_5222521 : CollatzResearch.WordTrace tailWord_5222521 prefixEnd_5222521 893887833733222198756523 := by
  unfold tailWord_5222521
  simp only [CollatzResearch.WordTrace]
  refine ⟨190480989512705827421291417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126987326341803884947527611 190480989512705827421291417)
  ·
    refine ⟨142860742134529370565968563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190480989512705827421291417 142860742134529370565968563)
    ·
      refine ⟨214291113201794055848952845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142860742134529370565968563 214291113201794055848952845)
      ·
        refine ⟨80359167450672770943357317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 214291113201794055848952845 80359167450672770943357317)
        ·
          refine ⟨15067343897001144551879497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80359167450672770943357317 15067343897001144551879497)
          ·
            refine ⟨11300507922750858413909623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15067343897001144551879497 11300507922750858413909623)
            ·
              refine ⟨16950761884126287620864435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11300507922750858413909623 16950761884126287620864435)
              ·
                refine ⟨25426142826189431431296653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16950761884126287620864435 25426142826189431431296653)
                ·
                  refine ⟨9534803559821036786736245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25426142826189431431296653 9534803559821036786736245)
                  ·
                    refine ⟨893887833733222198756523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9534803559821036786736245 893887833733222198756523)
                    ·
                      rfl

theorem cell23_5222521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 3, 5].length) (baseStart_5222521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5222521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5222521 prefixEnd_5222521 := by exact prefixLift 5222521
  have htrace : WordTrace (prefixWord ++ tailWord_5222521) baseStart_5222521 baseEnd_5222521 := by
    simpa [prefixWord, tailWord_5222521, baseEnd_5222521] using wordTrace_append hprefix tailTrace_5222521
  have hstable : (prefixWord ++ tailWord_5222521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5222521).length < 2 ^ (prefixWord ++ tailWord_5222521).sum := by decide
  have hdescent : baseEnd_5222521 < baseStart_5222521 := by decide
  rcases family_descends (prefixWord ++ tailWord_5222521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5222552 : List Nat := [2, 1, 2, 4, 3, 1, 1, 4, 1, 1, 3]
def baseStart_5222552 : Nat := 118140960795 + 5222552 * 2 ^ 59
def prefixEnd_5222552 : Nat := 4983230072969 + 3 ^ 40 * 5222552 * 2
def baseEnd_5222552 : Nat := 2681679419099955974981927

theorem tailTrace_5222552 : CollatzResearch.WordTrace tailWord_5222552 prefixEnd_5222552 2681679419099955974981927 := by
  unfold tailWord_5222552
  simp only [CollatzResearch.WordTrace]
  refine ⟨95241060087796759857834955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126988080117062346477113273 95241060087796759857834955)
  ·
    refine ⟨142861590131695139786752433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95241060087796759857834955 142861590131695139786752433)
    ·
      refine ⟨107146192598771354840064325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142861590131695139786752433 107146192598771354840064325)
      ·
        refine ⟨20089911112269629032512061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107146192598771354840064325 20089911112269629032512061)
        ·
          refine ⟨7533716667101110887192023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20089911112269629032512061 7533716667101110887192023)
          ·
            refine ⟨11300575000651666330788035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7533716667101110887192023 11300575000651666330788035)
            ·
              refine ⟨16950862500977499496182053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11300575000651666330788035 16950862500977499496182053)
              ·
                refine ⟨3178286718933281155534135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16950862500977499496182053 3178286718933281155534135)
                ·
                  refine ⟨4767430078399921733301203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3178286718933281155534135 4767430078399921733301203)
                  ·
                    refine ⟨7151145117599882599951805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4767430078399921733301203 7151145117599882599951805)
                    ·
                      refine ⟨2681679419099955974981927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7151145117599882599951805 2681679419099955974981927)
                      ·
                        rfl

theorem cell23_5222552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 4, 1, 1, 3].length) (baseStart_5222552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5222552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5222552 prefixEnd_5222552 := by exact prefixLift 5222552
  have htrace : WordTrace (prefixWord ++ tailWord_5222552) baseStart_5222552 baseEnd_5222552 := by
    simpa [prefixWord, tailWord_5222552, baseEnd_5222552] using wordTrace_append hprefix tailTrace_5222552
  have hstable : (prefixWord ++ tailWord_5222552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5222552).length < 2 ^ (prefixWord ++ tailWord_5222552).sum := by decide
  have hdescent : baseEnd_5222552 < baseStart_5222552 := by decide
  rcases family_descends (prefixWord ++ tailWord_5222552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5222578 : List Nat := [3, 2, 1, 1, 1, 3, 2, 4, 1, 2, 3]
def baseStart_5222578 : Nat := 118140960795 + 5222578 * 2 ^ 59
def prefixEnd_5222578 : Nat := 4983230072969 + 3 ^ 40 * 5222578 * 2
def baseEnd_5222578 : Nat := 2681692769596972873256807

theorem tailTrace_5222578 : CollatzResearch.WordTrace tailWord_5222578 prefixEnd_5222578 2681692769596972873256807 := by
  unfold tailWord_5222578
  simp only [CollatzResearch.WordTrace]
  refine ⟨47620767118374831539029097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126988712315666217437410925 47620767118374831539029097)
  ·
    refine ⟨35715575338781123654271823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47620767118374831539029097 35715575338781123654271823)
    ·
      refine ⟨53573363008171685481407735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35715575338781123654271823 53573363008171685481407735)
      ·
        refine ⟨80360044512257528222111603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53573363008171685481407735 80360044512257528222111603)
        ·
          refine ⟨120540066768386292333167405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80360044512257528222111603 120540066768386292333167405)
          ·
            refine ⟨45202525038144859624937777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120540066768386292333167405 45202525038144859624937777)
            ·
              refine ⟨33901893778608644718703333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45202525038144859624937777 33901893778608644718703333)
              ·
                refine ⟨6356605083489120884756875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33901893778608644718703333 6356605083489120884756875)
                ·
                  refine ⟨9534907625233681327135313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6356605083489120884756875 9534907625233681327135313)
                  ·
                    refine ⟨7151180718925260995351485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9534907625233681327135313 7151180718925260995351485)
                    ·
                      refine ⟨2681692769596972873256807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7151180718925260995351485 2681692769596972873256807)
                      ·
                        rfl

theorem cell23_5222578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 4, 1, 2, 3].length) (baseStart_5222578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5222578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5222578 prefixEnd_5222578 := by exact prefixLift 5222578
  have htrace : WordTrace (prefixWord ++ tailWord_5222578) baseStart_5222578 baseEnd_5222578 := by
    simpa [prefixWord, tailWord_5222578, baseEnd_5222578] using wordTrace_append hprefix tailTrace_5222578
  have hstable : (prefixWord ++ tailWord_5222578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5222578).length < 2 ^ (prefixWord ++ tailWord_5222578).sum := by decide
  have hdescent : baseEnd_5222578 < baseStart_5222578 := by decide
  rcases family_descends (prefixWord ++ tailWord_5222578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5222592 : List Nat := [2, 1, 1, 2, 5, 1, 1, 5, 1, 2, 2]
def baseStart_5222592 : Nat := 118140960795 + 5222592 * 2 ^ 59
def prefixEnd_5222592 : Nat := 4983230072969 + 3 ^ 40 * 5222592 * 2
def baseEnd_5222592 : Nat := 2681699958326135818481743

theorem tailTrace_5222592 : CollatzResearch.WordTrace tailWord_5222592 prefixEnd_5222592 2681699958326135818481743 := by
  unfold tailWord_5222592
  simp only [CollatzResearch.WordTrace]
  refine ⟨95241789547724303273563015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126989052730299071031417353 95241789547724303273563015)
  ·
    refine ⟨142862684321586454910344523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95241789547724303273563015 142862684321586454910344523)
    ·
      refine ⟨214294026482379682365516785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142862684321586454910344523 214294026482379682365516785)
      ·
        refine ⟨160720519861784761774137589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214294026482379682365516785 160720519861784761774137589)
        ·
          refine ⟨15067548737042321416325399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 160720519861784761774137589 15067548737042321416325399)
          ·
            refine ⟨22601323105563482124488099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15067548737042321416325399 22601323105563482124488099)
            ·
              refine ⟨33901984658345223186732149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22601323105563482124488099 33901984658345223186732149)
              ·
                refine ⟨3178311061719864673756139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33901984658345223186732149 3178311061719864673756139)
                ·
                  refine ⟨4767466592579797010634209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3178311061719864673756139 4767466592579797010634209)
                  ·
                    refine ⟨3575599944434847757975657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4767466592579797010634209 3575599944434847757975657)
                    ·
                      refine ⟨2681699958326135818481743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3575599944434847757975657 2681699958326135818481743)
                      ·
                        rfl

theorem cell23_5222592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 5, 1, 2, 2].length) (baseStart_5222592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5222592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5222592 prefixEnd_5222592 := by exact prefixLift 5222592
  have htrace : WordTrace (prefixWord ++ tailWord_5222592) baseStart_5222592 baseEnd_5222592 := by
    simpa [prefixWord, tailWord_5222592, baseEnd_5222592] using wordTrace_append hprefix tailTrace_5222592
  have hstable : (prefixWord ++ tailWord_5222592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5222592).length < 2 ^ (prefixWord ++ tailWord_5222592).sum := by decide
  have hdescent : baseEnd_5222592 < baseStart_5222592 := by decide
  rcases family_descends (prefixWord ++ tailWord_5222592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5222618 : List Nat := [3, 1, 1, 2, 2, 1, 2, 1, 5, 3, 2]
def baseStart_5222618 : Nat := 118140960795 + 5222618 * 2 ^ 59
def prefixEnd_5222618 : Nat := 4983230072969 + 3 ^ 40 * 5222618 * 2
def baseEnd_5222618 : Nat := 2681713308823152716756623

theorem tailTrace_5222618 : CollatzResearch.WordTrace tailWord_5222618 prefixEnd_5222618 2681713308823152716756623 := by
  unfold tailWord_5222618
  simp only [CollatzResearch.WordTrace]
  refine ⟨47621131848338603246893127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126989684928902941991715005 47621131848338603246893127)
  ·
    refine ⟨71431697772507904870339691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47621131848338603246893127 71431697772507904870339691)
    ·
      refine ⟨107147546658761857305509537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71431697772507904870339691 107147546658761857305509537)
      ·
        refine ⟨80360659994071392979132153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107147546658761857305509537 80360659994071392979132153)
        ·
          refine ⟨60270494995553544734349115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80360659994071392979132153 60270494995553544734349115)
          ·
            refine ⟨90405742493330317101523673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60270494995553544734349115 90405742493330317101523673)
            ·
              refine ⟨67804306869997737826142755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90405742493330317101523673 67804306869997737826142755)
              ·
                refine ⟨101706460304996606739214133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67804306869997737826142755 101706460304996606739214133)
                ·
                  refine ⟨9534980653593431881801325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 101706460304996606739214133 9534980653593431881801325)
                  ·
                    refine ⟨3575617745097536955675497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9534980653593431881801325 3575617745097536955675497)
                    ·
                      refine ⟨2681713308823152716756623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3575617745097536955675497 2681713308823152716756623)
                      ·
                        rfl

theorem cell23_5222618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 5, 3, 2].length) (baseStart_5222618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5222618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5222618 prefixEnd_5222618 := by exact prefixLift 5222618
  have htrace : WordTrace (prefixWord ++ tailWord_5222618) baseStart_5222618 baseEnd_5222618 := by
    simpa [prefixWord, tailWord_5222618, baseEnd_5222618] using wordTrace_append hprefix tailTrace_5222618
  have hstable : (prefixWord ++ tailWord_5222618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5222618).length < 2 ^ (prefixWord ++ tailWord_5222618).sum := by decide
  have hdescent : baseEnd_5222618 < baseStart_5222618 := by decide
  rcases family_descends (prefixWord ++ tailWord_5222618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5222635 : List Nat := [1, 1, 1, 1, 2, 5, 4, 2, 1, 3, 2]
def baseStart_5222635 : Nat := 118140960795 + 5222635 * 2 ^ 59
def prefixEnd_5222635 : Nat := 4983230072969 + 3 ^ 40 * 5222635 * 2
def baseEnd_5222635 : Nat := 2681722037994279150244045

theorem tailTrace_5222635 : CollatzResearch.WordTrace tailWord_5222635 prefixEnd_5222635 2681722037994279150244045 := by
  unfold tailWord_5222635
  simp only [CollatzResearch.WordTrace]
  refine ⟨190485147434292824890941359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126990098289528549927294239 190485147434292824890941359)
  ·
    refine ⟨285727721151439237336412039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190485147434292824890941359 285727721151439237336412039)
    ·
      refine ⟨428591581727158856004618059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285727721151439237336412039 428591581727158856004618059)
      ·
        refine ⟨642887372590738284006927089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 428591581727158856004618059 642887372590738284006927089)
        ·
          refine ⟨482165529443053713005195317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 642887372590738284006927089 482165529443053713005195317)
          ·
            refine ⟨45203018385286285594237061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 482165529443053713005195317 45203018385286285594237061)
            ·
              refine ⟨8475565947241178548919449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45203018385286285594237061 8475565947241178548919449)
              ·
                refine ⟨6356674460430883911689587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8475565947241178548919449 6356674460430883911689587)
                ·
                  refine ⟨9535011690646325867534381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6356674460430883911689587 9535011690646325867534381)
                  ·
                    refine ⟨3575629383992372200325393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9535011690646325867534381 3575629383992372200325393)
                    ·
                      refine ⟨2681722037994279150244045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3575629383992372200325393 2681722037994279150244045)
                      ·
                        rfl

theorem cell23_5222635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 2, 1, 3, 2].length) (baseStart_5222635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5222635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5222635 prefixEnd_5222635 := by exact prefixLift 5222635
  have htrace : WordTrace (prefixWord ++ tailWord_5222635) baseStart_5222635 baseEnd_5222635 := by
    simpa [prefixWord, tailWord_5222635, baseEnd_5222635] using wordTrace_append hprefix tailTrace_5222635
  have hstable : (prefixWord ++ tailWord_5222635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5222635).length < 2 ^ (prefixWord ++ tailWord_5222635).sum := by decide
  have hdescent : baseEnd_5222635 < baseStart_5222635 := by decide
  rcases family_descends (prefixWord ++ tailWord_5222635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5222648 : List Nat := [2, 1, 2, 1, 1, 2, 1, 6, 1, 4, 2]
def baseStart_5222648 : Nat := 118140960795 + 5222648 * 2 ^ 59
def prefixEnd_5222648 : Nat := 4983230072969 + 3 ^ 40 * 5222648 * 2
def baseEnd_5222648 : Nat := 2681728713242787599381485

theorem tailTrace_5222648 : CollatzResearch.WordTrace tailWord_5222648 prefixEnd_5222648 2681728713242787599381485 := by
  unfold tailWord_5222648
  simp only [CollatzResearch.WordTrace]
  refine ⟨95242810791622864055582299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126990414388830485407443065 95242810791622864055582299)
  ·
    refine ⟨142864216187434296083373449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95242810791622864055582299 142864216187434296083373449)
    ·
      refine ⟨107148162140575722062530087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142864216187434296083373449 107148162140575722062530087)
      ·
        refine ⟨160722243210863583093795131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107148162140575722062530087 160722243210863583093795131)
        ·
          refine ⟨241083364816295374640692697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160722243210863583093795131 241083364816295374640692697)
          ·
            refine ⟨180812523612221530980519523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 241083364816295374640692697 180812523612221530980519523)
            ·
              refine ⟨271218785418332296470779285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180812523612221530980519523 271218785418332296470779285)
              ·
                refine ⟨12713380566484326397067779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 271218785418332296470779285 12713380566484326397067779)
                ·
                  refine ⟨19070070849726489595601669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12713380566484326397067779 19070070849726489595601669)
                  ·
                    refine ⟨3575638284323716799175313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19070070849726489595601669 3575638284323716799175313)
                    ·
                      refine ⟨2681728713242787599381485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3575638284323716799175313 2681728713242787599381485)
                      ·
                        rfl

theorem cell23_5222648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 6, 1, 4, 2].length) (baseStart_5222648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5222648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5222648 prefixEnd_5222648 := by exact prefixLift 5222648
  have htrace : WordTrace (prefixWord ++ tailWord_5222648) baseStart_5222648 baseEnd_5222648 := by
    simpa [prefixWord, tailWord_5222648, baseEnd_5222648] using wordTrace_append hprefix tailTrace_5222648
  have hstable : (prefixWord ++ tailWord_5222648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5222648).length < 2 ^ (prefixWord ++ tailWord_5222648).sum := by decide
  have hdescent : baseEnd_5222648 < baseStart_5222648 := by decide
  rcases family_descends (prefixWord ++ tailWord_5222648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5222661 : List Nat := [1, 3, 1, 1, 2, 1, 2, 4, 2, 2, 4]
def baseStart_5222661 : Nat := 118140960795 + 5222661 * 2 ^ 59
def prefixEnd_5222661 : Nat := 4983230072969 + 3 ^ 40 * 5222661 * 2
def baseEnd_5222661 : Nat := 2681735388491296048518925

theorem tailTrace_5222661 : CollatzResearch.WordTrace tailWord_5222661 prefixEnd_5222661 2681735388491296048518925 := by
  unfold tailWord_5222661
  simp only [CollatzResearch.WordTrace]
  refine ⟨190486095732198631331387837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126990730488132420887591891 190486095732198631331387837)
  ·
    refine ⟨71432285899574486749270439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190486095732198631331387837 71432285899574486749270439)
    ·
      refine ⟨107148428849361730123905659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71432285899574486749270439 107148428849361730123905659)
      ·
        refine ⟨160722643274042595185858489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107148428849361730123905659 160722643274042595185858489)
        ·
          refine ⟨120541982455531946389393867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160722643274042595185858489 120541982455531946389393867)
          ·
            refine ⟨180812973683297919584090801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120541982455531946389393867 180812973683297919584090801)
            ·
              refine ⟨135609730262473439688068101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 180812973683297919584090801 135609730262473439688068101)
              ·
                refine ⟨25426824424213769941512769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 135609730262473439688068101 25426824424213769941512769)
                ·
                  refine ⟨19070118318160327456134577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25426824424213769941512769 19070118318160327456134577)
                  ·
                    refine ⟨14302588738620245592100933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19070118318160327456134577 14302588738620245592100933)
                    ·
                      refine ⟨2681735388491296048518925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14302588738620245592100933 2681735388491296048518925)
                      ·
                        rfl

theorem cell23_5222661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 2, 2, 4].length) (baseStart_5222661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5222661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5222661 prefixEnd_5222661 := by exact prefixLift 5222661
  have htrace : WordTrace (prefixWord ++ tailWord_5222661) baseStart_5222661 baseEnd_5222661 := by
    simpa [prefixWord, tailWord_5222661, baseEnd_5222661] using wordTrace_append hprefix tailTrace_5222661
  have hstable : (prefixWord ++ tailWord_5222661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5222661).length < 2 ^ (prefixWord ++ tailWord_5222661).sum := by decide
  have hdescent : baseEnd_5222661 < baseStart_5222661 := by decide
  rcases family_descends (prefixWord ++ tailWord_5222661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5222665 : List Nat := [1, 2, 1, 1, 3, 4, 2, 1, 4, 2, 2]
def baseStart_5222665 : Nat := 118140960795 + 5222665 * 2 ^ 59
def prefixEnd_5222665 : Nat := 4983230072969 + 3 ^ 40 * 5222665 * 2
def baseEnd_5222665 : Nat := 2681737442413914032868907

theorem tailTrace_5222665 : CollatzResearch.WordTrace tailWord_5222665 prefixEnd_5222665 2681737442413914032868907 := by
  unfold tailWord_5222665
  simp only [CollatzResearch.WordTrace]
  refine ⟨190486241624184140014533449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126990827749456093343022299 190486241624184140014533449)
  ·
    refine ⟨142864681218138105010900087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190486241624184140014533449 142864681218138105010900087)
    ·
      refine ⟨214297021827207157516350131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142864681218138105010900087 214297021827207157516350131)
      ·
        refine ⟨321445532740810736274525197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214297021827207157516350131 321445532740810736274525197)
        ·
          refine ⟨120542074777804026102946949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 321445532740810736274525197 120542074777804026102946949)
          ·
            refine ⟨22601639020838254894302553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 120542074777804026102946949 22601639020838254894302553)
            ·
              refine ⟨16951229265628691170726915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22601639020838254894302553 16951229265628691170726915)
              ·
                refine ⟨25426843898443036756090373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16951229265628691170726915 25426843898443036756090373)
                ·
                  refine ⟨4767533230958069391766945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25426843898443036756090373 4767533230958069391766945)
                  ·
                    refine ⟨3575649923218552043825209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4767533230958069391766945 3575649923218552043825209)
                    ·
                      refine ⟨2681737442413914032868907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3575649923218552043825209 2681737442413914032868907)
                      ·
                        rfl

theorem cell23_5222665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 4, 2, 2].length) (baseStart_5222665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5222665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5222665 prefixEnd_5222665 := by exact prefixLift 5222665
  have htrace : WordTrace (prefixWord ++ tailWord_5222665) baseStart_5222665 baseEnd_5222665 := by
    simpa [prefixWord, tailWord_5222665, baseEnd_5222665] using wordTrace_append hprefix tailTrace_5222665
  have hstable : (prefixWord ++ tailWord_5222665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5222665).length < 2 ^ (prefixWord ++ tailWord_5222665).sum := by decide
  have hdescent : baseEnd_5222665 < baseStart_5222665 := by decide
  rcases family_descends (prefixWord ++ tailWord_5222665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5222686 : List Nat := [4, 3, 2, 1, 1, 3, 1, 2, 1, 3, 2]
def baseStart_5222686 : Nat := 118140960795 + 5222686 * 2 ^ 59
def prefixEnd_5222686 : Nat := 4983230072969 + 3 ^ 40 * 5222686 * 2
def baseEnd_5222686 : Nat := 2681748225507658450706311

theorem tailTrace_5222686 : CollatzResearch.WordTrace tailWord_5222686 prefixEnd_5222686 2681748225507658450706311 := by
  unfold tailWord_5222686
  simp only [CollatzResearch.WordTrace]
  refine ⟨23810875944638507575130989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126991338371405373734031941 23810875944638507575130989)
  ·
    refine ⟨8929078479239440340674121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23810875944638507575130989 8929078479239440340674121)
    ·
      refine ⟨6696808859429580255505591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8929078479239440340674121 6696808859429580255505591)
      ·
        refine ⟨10045213289144370383258387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6696808859429580255505591 10045213289144370383258387)
        ·
          refine ⟨15067819933716555574887581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10045213289144370383258387 15067819933716555574887581)
          ·
            refine ⟨5650432475143708340582843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15067819933716555574887581 5650432475143708340582843)
            ·
              refine ⟨8475648712715562510874265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5650432475143708340582843 8475648712715562510874265)
              ·
                refine ⟨6356736534536671883155699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8475648712715562510874265 6356736534536671883155699)
                ·
                  refine ⟨9535104801805007824733549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6356736534536671883155699 9535104801805007824733549)
                  ·
                    refine ⟨3575664300676877934275081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9535104801805007824733549 3575664300676877934275081)
                    ·
                      refine ⟨2681748225507658450706311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3575664300676877934275081 2681748225507658450706311)
                      ·
                        rfl

theorem cell23_5222686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_5222686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5222686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5222686 prefixEnd_5222686 := by exact prefixLift 5222686
  have htrace : WordTrace (prefixWord ++ tailWord_5222686) baseStart_5222686 baseEnd_5222686 := by
    simpa [prefixWord, tailWord_5222686, baseEnd_5222686] using wordTrace_append hprefix tailTrace_5222686
  have hstable : (prefixWord ++ tailWord_5222686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5222686).length < 2 ^ (prefixWord ++ tailWord_5222686).sum := by decide
  have hdescent : baseEnd_5222686 < baseStart_5222686 := by decide
  rcases family_descends (prefixWord ++ tailWord_5222686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5222738 : List Nat := [3, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4]
def baseStart_5222738 : Nat := 118140960795 + 5222738 * 2 ^ 59
def prefixEnd_5222738 : Nat := 4983230072969 + 3 ^ 40 * 5222738 * 2
def baseEnd_5222738 : Nat := 2681774926501692247256071

theorem tailTrace_5222738 : CollatzResearch.WordTrace tailWord_5222738 prefixEnd_5222738 2681774926501692247256071 := by
  unfold tailWord_5222738
  simp only [CollatzResearch.WordTrace]
  refine ⟨47622226038229918370485217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126992602768613115654627245 47622226038229918370485217)
  ·
    refine ⟨35716669528672438777863913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47622226038229918370485217 35716669528672438777863913)
    ·
      refine ⟨26787502146504329083397935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35716669528672438777863913 26787502146504329083397935)
      ·
        refine ⟨40181253219756493625096903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26787502146504329083397935 40181253219756493625096903)
        ·
          refine ⟨60271879829634740437645355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40181253219756493625096903 60271879829634740437645355)
          ·
            refine ⟨90407819744452110656468033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60271879829634740437645355 90407819744452110656468033)
            ·
              refine ⟨67805864808339082992351025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90407819744452110656468033 67805864808339082992351025)
              ·
                refine ⟨50854398606254312244263269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67805864808339082992351025 50854398606254312244263269)
                ·
                  refine ⟨9535199738672683545799363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50854398606254312244263269 9535199738672683545799363)
                  ·
                    refine ⟨14302799608009025318699045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9535199738672683545799363 14302799608009025318699045)
                    ·
                      refine ⟨2681774926501692247256071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14302799608009025318699045 2681774926501692247256071)
                      ·
                        rfl

theorem cell23_5222738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_5222738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5222738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5222738 prefixEnd_5222738 := by exact prefixLift 5222738
  have htrace : WordTrace (prefixWord ++ tailWord_5222738) baseStart_5222738 baseEnd_5222738 := by
    simpa [prefixWord, tailWord_5222738, baseEnd_5222738] using wordTrace_append hprefix tailTrace_5222738
  have hstable : (prefixWord ++ tailWord_5222738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5222738).length < 2 ^ (prefixWord ++ tailWord_5222738).sum := by decide
  have hdescent : baseEnd_5222738 < baseStart_5222738 := by decide
  rcases family_descends (prefixWord ++ tailWord_5222738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5222752 : List Nat := [2, 1, 1, 3, 6, 1, 1, 1, 2, 5]
def baseStart_5222752 : Nat := 118140960795 + 5222752 * 2 ^ 59
def prefixEnd_5222752 : Nat := 4983230072969 + 3 ^ 40 * 5222752 * 2
def baseEnd_5222752 : Nat := 893927371743618397493669

theorem tailTrace_5222752 : CollatzResearch.WordTrace tailWord_5222752 prefixEnd_5222752 893927371743618397493669 := by
  unfold tailWord_5222752
  simp only [CollatzResearch.WordTrace]
  refine ⟨95244707387434476936475255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126992943183245969248633673 95244707387434476936475255)
  ·
    refine ⟨142867061081151715404712883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95244707387434476936475255 142867061081151715404712883)
    ·
      refine ⟨214300591621727573107069325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142867061081151715404712883 214300591621727573107069325)
      ·
        refine ⟨80362721858147839915150997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 214300591621727573107069325 80362721858147839915150997)
        ·
          refine ⟨3767002587100679996022703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 80362721858147839915150997 3767002587100679996022703)
          ·
            refine ⟨5650503880651019994034055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3767002587100679996022703 5650503880651019994034055)
            ·
              refine ⟨8475755820976529991051083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5650503880651019994034055 8475755820976529991051083)
              ·
                refine ⟨12713633731464794986576625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8475755820976529991051083 12713633731464794986576625)
                ·
                  refine ⟨9535225298598596239932469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12713633731464794986576625 9535225298598596239932469)
                  ·
                    refine ⟨893927371743618397493669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9535225298598596239932469 893927371743618397493669)
                    ·
                      rfl

theorem cell23_5222752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 1, 2, 5].length) (baseStart_5222752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5222752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5222752 prefixEnd_5222752 := by exact prefixLift 5222752
  have htrace : WordTrace (prefixWord ++ tailWord_5222752) baseStart_5222752 baseEnd_5222752 := by
    simpa [prefixWord, tailWord_5222752, baseEnd_5222752] using wordTrace_append hprefix tailTrace_5222752
  have hstable : (prefixWord ++ tailWord_5222752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5222752).length < 2 ^ (prefixWord ++ tailWord_5222752).sum := by decide
  have hdescent : baseEnd_5222752 < baseStart_5222752 := by decide
  rcases family_descends (prefixWord ++ tailWord_5222752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5222761 : List Nat := [1, 2, 1, 1, 1, 3, 4, 2, 8]
def baseStart_5222761 : Nat := 118140960795 + 5222761 * 2 ^ 59
def prefixEnd_5222761 : Nat := 4983230072969 + 3 ^ 40 * 5222761 * 2
def baseEnd_5222761 : Nat := 297976304061860628585385

theorem tailTrace_5222761 : CollatzResearch.WordTrace tailWord_5222761 prefixEnd_5222761 297976304061860628585385 := by
  unfold tailWord_5222761
  simp only [CollatzResearch.WordTrace]
  refine ⟨190489743031836348410028137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126993162021224232273352091 190489743031836348410028137)
  ·
    refine ⟨142867307273877261307521103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190489743031836348410028137 142867307273877261307521103)
    ·
      refine ⟨214300960910815891961281655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142867307273877261307521103 214300960910815891961281655)
      ·
        refine ⟨321451441366223837941922483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214300960910815891961281655 321451441366223837941922483)
        ·
          refine ⟨482177162049335756912883725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 321451441366223837941922483 482177162049335756912883725)
          ·
            refine ⟨180816435768500908842331397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 482177162049335756912883725 180816435768500908842331397)
            ·
              refine ⟨33903081706593920407937137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 180816435768500908842331397 33903081706593920407937137)
              ·
                refine ⟨25427311279945440305952853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33903081706593920407937137 25427311279945440305952853)
                ·
                  refine ⟨297976304061860628585385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25427311279945440305952853 297976304061860628585385)
                  ·
                    rfl

theorem cell23_5222761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 8].length) (baseStart_5222761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5222761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5222761 prefixEnd_5222761 := by exact prefixLift 5222761
  have htrace : WordTrace (prefixWord ++ tailWord_5222761) baseStart_5222761 baseEnd_5222761 := by
    simpa [prefixWord, tailWord_5222761, baseEnd_5222761] using wordTrace_append hprefix tailTrace_5222761
  have hstable : (prefixWord ++ tailWord_5222761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5222761).length < 2 ^ (prefixWord ++ tailWord_5222761).sum := by decide
  have hdescent : baseEnd_5222761 < baseStart_5222761 := by decide
  rcases family_descends (prefixWord ++ tailWord_5222761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5222795 : List Nat := [1, 1, 1, 1, 4, 5, 3, 1, 6]
def baseStart_5222795 : Nat := 118140960795 + 5222795 * 2 ^ 59
def prefixEnd_5222795 : Nat := 4983230072969 + 3 ^ 40 * 5222795 * 2
def baseEnd_5222795 : Nat := 297978243877666502693701

theorem tailTrace_5222795 : CollatzResearch.WordTrace tailWord_5222795 prefixEnd_5222795 297978243877666502693701 := by
  unfold tailWord_5222795
  simp only [CollatzResearch.WordTrace]
  refine ⟨190490983113713172216765839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126993988742475448144510559 190490983113713172216765839)
  ·
    refine ⟨285736474670569758325148759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190490983113713172216765839 285736474670569758325148759)
    ·
      refine ⟨428604712005854637487723139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285736474670569758325148759 428604712005854637487723139)
      ·
        refine ⟨642907068008781956231584709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 428604712005854637487723139 642907068008781956231584709)
        ·
          refine ⟨120545075251646616793422133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 642907068008781956231584709 120545075251646616793422133)
          ·
            refine ⟨11301100804841870324383325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 120545075251646616793422133 11301100804841870324383325)
            ·
              refine ⟨4237912801815701371643747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11301100804841870324383325 4237912801815701371643747)
              ·
                refine ⟨6356869202723552057465621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4237912801815701371643747 6356869202723552057465621)
                ·
                  refine ⟨297978243877666502693701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6356869202723552057465621 297978243877666502693701)
                  ·
                    rfl

theorem cell23_5222795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 3, 1, 6].length) (baseStart_5222795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5222795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5222795 prefixEnd_5222795 := by exact prefixLift 5222795
  have htrace : WordTrace (prefixWord ++ tailWord_5222795) baseStart_5222795 baseEnd_5222795 := by
    simpa [prefixWord, tailWord_5222795, baseEnd_5222795] using wordTrace_append hprefix tailTrace_5222795
  have hstable : (prefixWord ++ tailWord_5222795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5222795).length < 2 ^ (prefixWord ++ tailWord_5222795).sum := by decide
  have hdescent : baseEnd_5222795 < baseStart_5222795 := by decide
  rcases family_descends (prefixWord ++ tailWord_5222795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5222815 : List Nat := [1, 1, 2, 5, 1, 1, 1, 3, 1, 5, 2]
def baseStart_5222815 : Nat := 118140960795 + 5222815 * 2 ^ 59
def prefixEnd_5222815 : Nat := 4983230072969 + 3 ^ 40 * 5222815 * 2
def baseEnd_5222815 : Nat := 2681814464512088445993217

theorem tailTrace_5222815 : CollatzResearch.WordTrace tailWord_5222815 prefixEnd_5222815 2681814464512088445993217 := by
  unfold tailWord_5222815
  simp only [CollatzResearch.WordTrace]
  refine ⟨190491712573640715632493899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126994475049093810421662599 190491712573640715632493899)
  ·
    refine ⟨285737568860461073448740849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190491712573640715632493899 285737568860461073448740849)
    ·
      refine ⟨214303176645345805086555637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 285737568860461073448740849 214303176645345805086555637)
      ·
        refine ⟨20090922810501169226864591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 214303176645345805086555637 20090922810501169226864591)
        ·
          refine ⟨30136384215751753840296887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20090922810501169226864591 30136384215751753840296887)
          ·
            refine ⟨45204576323627630760445331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30136384215751753840296887 45204576323627630760445331)
            ·
              refine ⟨67806864485441446140667997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45204576323627630760445331 67806864485441446140667997)
              ·
                refine ⟨25427574182040542302750499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67806864485441446140667997 25427574182040542302750499)
                ·
                  refine ⟨38141361273060813454125749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25427574182040542302750499 38141361273060813454125749)
                  ·
                    refine ⟨3575752619349451261324289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38141361273060813454125749 3575752619349451261324289)
                    ·
                      refine ⟨2681814464512088445993217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3575752619349451261324289 2681814464512088445993217)
                      ·
                        rfl

theorem cell23_5222815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 5, 2].length) (baseStart_5222815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5222815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5222815 prefixEnd_5222815 := by exact prefixLift 5222815
  have htrace : WordTrace (prefixWord ++ tailWord_5222815) baseStart_5222815 baseEnd_5222815 := by
    simpa [prefixWord, tailWord_5222815, baseEnd_5222815] using wordTrace_append hprefix tailTrace_5222815
  have hstable : (prefixWord ++ tailWord_5222815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5222815).length < 2 ^ (prefixWord ++ tailWord_5222815).sum := by decide
  have hdescent : baseEnd_5222815 < baseStart_5222815 := by decide
  rcases family_descends (prefixWord ++ tailWord_5222815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5222826 : List Nat := [3, 1, 6, 1, 1, 1, 1, 2, 2, 2, 3]
def baseStart_5222826 : Nat := 118140960795 + 5222826 * 2 ^ 59
def prefixEnd_5222826 : Nat := 4983230072969 + 3 ^ 40 * 5222826 * 2
def baseEnd_5222826 : Nat := 2681820112799287902955667

theorem tailTrace_5222826 : CollatzResearch.WordTrace tailWord_5222826 prefixEnd_5222826 2681820112799287902955667 := by
  unfold tailWord_5222826
  simp only [CollatzResearch.WordTrace]
  refine ⟨47623028444150216127786083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126994742517733909674096221 47623028444150216127786083)
  ·
    refine ⟨71434542666225324191679125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47623028444150216127786083 71434542666225324191679125)
    ·
      refine ⟨3348494187479312071484959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 71434542666225324191679125 3348494187479312071484959)
      ·
        refine ⟨5022741281218968107227439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3348494187479312071484959 5022741281218968107227439)
        ·
          refine ⟨7534111921828452160841159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5022741281218968107227439 7534111921828452160841159)
          ·
            refine ⟨11301167882742678241261739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7534111921828452160841159 11301167882742678241261739)
            ·
              refine ⟨16951751824114017361892609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11301167882742678241261739 16951751824114017361892609)
              ·
                refine ⟨12713813868085513021419457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16951751824114017361892609 12713813868085513021419457)
                ·
                  refine ⟨9535360401064134766064593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12713813868085513021419457 9535360401064134766064593)
                  ·
                    refine ⟨7151520300798101074548445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9535360401064134766064593 7151520300798101074548445)
                    ·
                      refine ⟨2681820112799287902955667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7151520300798101074548445 2681820112799287902955667)
                      ·
                        rfl

theorem cell23_5222826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_5222826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5222826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5222826 prefixEnd_5222826 := by exact prefixLift 5222826
  have htrace : WordTrace (prefixWord ++ tailWord_5222826) baseStart_5222826 baseEnd_5222826 := by
    simpa [prefixWord, tailWord_5222826, baseEnd_5222826] using wordTrace_append hprefix tailTrace_5222826
  have hstable : (prefixWord ++ tailWord_5222826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5222826).length < 2 ^ (prefixWord ++ tailWord_5222826).sum := by decide
  have hdescent : baseEnd_5222826 < baseStart_5222826 := by decide
  rcases family_descends (prefixWord ++ tailWord_5222826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5222828 : List Nat := [2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 4]
def baseStart_5222828 : Nat := 118140960795 + 5222828 * 2 ^ 59
def prefixEnd_5222828 : Nat := 4983230072969 + 3 ^ 40 * 5222828 * 2
def baseEnd_5222828 : Nat := 2681821139760596895130657

theorem tailTrace_5222828 : CollatzResearch.WordTrace tailWord_5222828 prefixEnd_5222828 2681821139760596895130657 := by
  unfold tailWord_5222828
  simp only [CollatzResearch.WordTrace]
  refine ⟨95246093361296809426358569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126994791148395745901811425 95246093361296809426358569)
  ·
    refine ⟨71434570020972607069768927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95246093361296809426358569 71434570020972607069768927)
    ·
      refine ⟨107151855031458910604653391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71434570020972607069768927 107151855031458910604653391)
      ·
        refine ⟨160727782547188365906980087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107151855031458910604653391 160727782547188365906980087)
        ·
          refine ⟨241091673820782548860470131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160727782547188365906980087 241091673820782548860470131)
          ·
            refine ⟨361637510731173823290705197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241091673820782548860470131 361637510731173823290705197)
            ·
              refine ⟨135614066524190183734014449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 361637510731173823290705197 135614066524190183734014449)
              ·
                refine ⟨101710549893142637800510837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 135614066524190183734014449 101710549893142637800510837)
                ·
                  refine ⟨9535364052482122293797891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 101710549893142637800510837 9535364052482122293797891)
                  ·
                    refine ⟨14303046078723183440696837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9535364052482122293797891 14303046078723183440696837)
                    ·
                      refine ⟨2681821139760596895130657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14303046078723183440696837 2681821139760596895130657)
                      ·
                        rfl

theorem cell23_5222828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 4].length) (baseStart_5222828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5222828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5222828 prefixEnd_5222828 := by exact prefixLift 5222828
  have htrace : WordTrace (prefixWord ++ tailWord_5222828) baseStart_5222828 baseEnd_5222828 := by
    simpa [prefixWord, tailWord_5222828, baseEnd_5222828] using wordTrace_append hprefix tailTrace_5222828
  have hstable : (prefixWord ++ tailWord_5222828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5222828).length < 2 ^ (prefixWord ++ tailWord_5222828).sum := by decide
  have hdescent : baseEnd_5222828 < baseStart_5222828 := by decide
  rcases family_descends (prefixWord ++ tailWord_5222828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5222848 : List Nat := [2, 1, 1, 2, 3, 1, 1, 1, 2, 6, 3]
def baseStart_5222848 : Nat := 118140960795 + 5222848 * 2 ^ 59
def prefixEnd_5222848 : Nat := 4983230072969 + 3 ^ 40 * 5222848 * 2
def baseEnd_5222848 : Nat := 2681831409373686816880565

theorem tailTrace_5222848 : CollatzResearch.WordTrace tailWord_5222848 prefixEnd_5222848 2681831409373686816880565 := by
  unfold tailWord_5222848
  simp only [CollatzResearch.WordTrace]
  refine ⟨95246458091260581134222599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126995277455014108178963465 95246458091260581134222599)
  ·
    refine ⟨142869687136890871701333899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95246458091260581134222599 142869687136890871701333899)
    ·
      refine ⟨214304530705336307552000849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142869687136890871701333899 214304530705336307552000849)
      ·
        refine ⟨160728398029002230664000637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214304530705336307552000849 160728398029002230664000637)
        ·
          refine ⟨60273149260875836499000239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 160728398029002230664000637 60273149260875836499000239)
          ·
            refine ⟨90409723891313754748500359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60273149260875836499000239 90409723891313754748500359)
            ·
              refine ⟨135614585836970632122750539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90409723891313754748500359 135614585836970632122750539)
              ·
                refine ⟨203421878755455948184125809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135614585836970632122750539 203421878755455948184125809)
                ·
                  refine ⟨152566409066591961138094357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 203421878755455948184125809 152566409066591961138094357)
                  ·
                    refine ⟨7151550424996498178348173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 152566409066591961138094357 7151550424996498178348173)
                    ·
                      refine ⟨2681831409373686816880565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7151550424996498178348173 2681831409373686816880565)
                      ·
                        rfl

theorem cell23_5222848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 2, 6, 3].length) (baseStart_5222848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5222848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5222848 prefixEnd_5222848 := by exact prefixLift 5222848
  have htrace : WordTrace (prefixWord ++ tailWord_5222848) baseStart_5222848 baseEnd_5222848 := by
    simpa [prefixWord, tailWord_5222848, baseEnd_5222848] using wordTrace_append hprefix tailTrace_5222848
  have hstable : (prefixWord ++ tailWord_5222848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5222848).length < 2 ^ (prefixWord ++ tailWord_5222848).sum := by decide
  have hdescent : baseEnd_5222848 < baseStart_5222848 := by decide
  rcases family_descends (prefixWord ++ tailWord_5222848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5222858 : List Nat := [3, 1, 2, 1, 2, 2, 1, 3, 1, 1, 6]
def baseStart_5222858 : Nat := 118140960795 + 5222858 * 2 ^ 59
def prefixEnd_5222858 : Nat := 4983230072969 + 3 ^ 40 * 5222858 * 2
def baseEnd_5222858 : Nat := 2681836544180231777755519

theorem tailTrace_5222858 : CollatzResearch.WordTrace tailWord_5222858 prefixEnd_5222858 2681836544180231777755519 := by
  unfold tailWord_5222858
  simp only [CollatzResearch.WordTrace]
  refine ⟨47623320228121233494077307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126995520608323289317539485 47623320228121233494077307)
  ·
    refine ⟨71434980342181850241115961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47623320228121233494077307 71434980342181850241115961)
    ·
      refine ⟨53576235256636387680836971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71434980342181850241115961 53576235256636387680836971)
      ·
        refine ⟨80364352884954581521255457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53576235256636387680836971 80364352884954581521255457)
        ·
          refine ⟨60273264663715936140941593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80364352884954581521255457 60273264663715936140941593)
          ·
            refine ⟨45204948497786952105706195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60273264663715936140941593 45204948497786952105706195)
            ·
              refine ⟨67807422746680428158559293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45204948497786952105706195 67807422746680428158559293)
              ·
                refine ⟨25427783530005160559459735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67807422746680428158559293 25427783530005160559459735)
                ·
                  refine ⟨38141675295007740839189603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25427783530005160559459735 38141675295007740839189603)
                  ·
                    refine ⟨57212512942511611258784405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38141675295007740839189603 57212512942511611258784405)
                    ·
                      refine ⟨2681836544180231777755519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57212512942511611258784405 2681836544180231777755519)
                      ·
                        rfl

theorem cell23_5222858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 1, 1, 6].length) (baseStart_5222858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5222858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5222858 prefixEnd_5222858 := by exact prefixLift 5222858
  have htrace : WordTrace (prefixWord ++ tailWord_5222858) baseStart_5222858 baseEnd_5222858 := by
    simpa [prefixWord, tailWord_5222858, baseEnd_5222858] using wordTrace_append hprefix tailTrace_5222858
  have hstable : (prefixWord ++ tailWord_5222858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5222858).length < 2 ^ (prefixWord ++ tailWord_5222858).sum := by decide
  have hdescent : baseEnd_5222858 < baseStart_5222858 := by decide
  rcases family_descends (prefixWord ++ tailWord_5222858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5222862 : List Nat := [4, 1, 1, 1, 2, 1, 1, 3, 5, 2, 2]
def baseStart_5222862 : Nat := 118140960795 + 5222862 * 2 ^ 59
def prefixEnd_5222862 : Nat := 4983230072969 + 3 ^ 40 * 5222862 * 2
def baseEnd_5222862 : Nat := 2681838598102849762105501

theorem tailTrace_5222862 : CollatzResearch.WordTrace tailWord_5222862 prefixEnd_5222862 2681838598102849762105501 := by
  unfold tailWord_5222862
  simp only [CollatzResearch.WordTrace]
  refine ⟨23811678350558805332431855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 126995617869646961772969893 23811678350558805332431855)
  ·
    refine ⟨35717517525838207998647783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23811678350558805332431855 35717517525838207998647783)
    ·
      refine ⟨53576276288757311997971675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35717517525838207998647783 53576276288757311997971675)
      ·
        refine ⟨80364414433135967996957513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53576276288757311997971675 80364414433135967996957513)
        ·
          refine ⟨60273310824851975997718135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80364414433135967996957513 60273310824851975997718135)
          ·
            refine ⟨90409966237277963996577203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60273310824851975997718135 90409966237277963996577203)
            ·
              refine ⟨135614949355916945994865805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90409966237277963996577203 135614949355916945994865805)
              ·
                refine ⟨50855606008468854748074677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 135614949355916945994865805 50855606008468854748074677)
                ·
                  refine ⟨4767713063293955132632001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50855606008468854748074677 4767713063293955132632001)
                  ·
                    refine ⟨3575784797470466349474001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4767713063293955132632001 3575784797470466349474001)
                    ·
                      refine ⟨2681838598102849762105501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3575784797470466349474001 2681838598102849762105501)
                      ·
                        rfl

theorem cell23_5222862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 5, 2, 2].length) (baseStart_5222862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5222862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5222862 prefixEnd_5222862 := by exact prefixLift 5222862
  have htrace : WordTrace (prefixWord ++ tailWord_5222862) baseStart_5222862 baseEnd_5222862 := by
    simpa [prefixWord, tailWord_5222862, baseEnd_5222862] using wordTrace_append hprefix tailTrace_5222862
  have hstable : (prefixWord ++ tailWord_5222862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5222862).length < 2 ^ (prefixWord ++ tailWord_5222862).sum := by decide
  have hdescent : baseEnd_5222862 < baseStart_5222862 := by decide
  rcases family_descends (prefixWord ++ tailWord_5222862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5222866 : List Nat := [3, 2, 2, 4, 1, 1, 2, 1, 2, 3, 2]
def baseStart_5222866 : Nat := 118140960795 + 5222866 * 2 ^ 59
def prefixEnd_5222866 : Nat := 4983230072969 + 3 ^ 40 * 5222866 * 2
def baseEnd_5222866 : Nat := 2681840652025467746455483

theorem tailTrace_5222866 : CollatzResearch.WordTrace tailWord_5222866 prefixEnd_5222866 2681840652025467746455483 := by
  unfold tailWord_5222866
  simp only [CollatzResearch.WordTrace]
  refine ⟨47623393174113987835650113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126995715130970634228400301 47623393174113987835650113)
  ·
    refine ⟨35717544880585490876737585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47623393174113987835650113 35717544880585490876737585)
    ·
      refine ⟨26788158660439118157553189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35717544880585490876737585 26788158660439118157553189)
      ·
        refine ⟨5022779748832334654541223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26788158660439118157553189 5022779748832334654541223)
        ·
          refine ⟨7534169623248501981811835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5022779748832334654541223 7534169623248501981811835)
          ·
            refine ⟨11301254434872752972717753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7534169623248501981811835 11301254434872752972717753)
            ·
              refine ⟨8475940826154564729538315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11301254434872752972717753 8475940826154564729538315)
              ·
                refine ⟨12713911239231847094307473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8475940826154564729538315 12713911239231847094307473)
                ·
                  refine ⟨9535433429423885320730605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12713911239231847094307473 9535433429423885320730605)
                  ·
                    refine ⟨3575787536033956995273977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9535433429423885320730605 3575787536033956995273977)
                    ·
                      refine ⟨2681840652025467746455483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3575787536033956995273977 2681840652025467746455483)
                      ·
                        rfl

theorem cell23_5222866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_5222866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5222866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5222866 prefixEnd_5222866 := by exact prefixLift 5222866
  have htrace : WordTrace (prefixWord ++ tailWord_5222866) baseStart_5222866 baseEnd_5222866 := by
    simpa [prefixWord, tailWord_5222866, baseEnd_5222866] using wordTrace_append hprefix tailTrace_5222866
  have hstable : (prefixWord ++ tailWord_5222866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5222866).length < 2 ^ (prefixWord ++ tailWord_5222866).sum := by decide
  have hdescent : baseEnd_5222866 < baseStart_5222866 := by decide
  rcases family_descends (prefixWord ++ tailWord_5222866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5222885 : List Nat := [1, 3, 1, 5, 3, 10]
def baseStart_5222885 : Nat := 118140960795 + 5222885 * 2 ^ 59
def prefixEnd_5222885 : Nat := 4983230072969 + 3 ^ 40 * 5222885 * 2
def baseEnd_5222885 : Nat := 11036421432748572724765

theorem tailTrace_5222885 : CollatzResearch.WordTrace tailWord_5222885 prefixEnd_5222885 11036421432748572724765 := by
  unfold tailWord_5222885
  simp only [CollatzResearch.WordTrace]
  refine ⟨190494265683387117587542109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126996177122258078391694739 190494265683387117587542109)
  ·
    refine ⟨71435349631270169095328291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190494265683387117587542109 71435349631270169095328291)
    ·
      refine ⟨107153024446905253642992437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71435349631270169095328291 107153024446905253642992437)
      ·
        refine ⟨10045596041897367529030541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 107153024446905253642992437 10045596041897367529030541)
        ·
          refine ⟨3767098515711512823386453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10045596041897367529030541 3767098515711512823386453)
          ·
            refine ⟨11036421432748572724765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3767098515711512823386453 11036421432748572724765)
            ·
              rfl

theorem cell23_5222885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 10].length) (baseStart_5222885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5222885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5222885 prefixEnd_5222885 := by exact prefixLift 5222885
  have htrace : WordTrace (prefixWord ++ tailWord_5222885) baseStart_5222885 baseEnd_5222885 := by
    simpa [prefixWord, tailWord_5222885, baseEnd_5222885] using wordTrace_append hprefix tailTrace_5222885
  have hstable : (prefixWord ++ tailWord_5222885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5222885).length < 2 ^ (prefixWord ++ tailWord_5222885).sum := by decide
  have hdescent : baseEnd_5222885 < baseStart_5222885 := by decide
  rcases family_descends (prefixWord ++ tailWord_5222885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5222908 : List Nat := [2, 2, 2, 1, 2, 1, 1, 2, 1, 4, 5]
def baseStart_5222908 : Nat := 118140960795 + 5222908 * 2 ^ 59
def prefixEnd_5222908 : Nat := 4983230072969 + 3 ^ 40 * 5222908 * 2
def baseEnd_5222908 : Nat := 2681862218212956582130289

theorem tailTrace_5222908 : CollatzResearch.WordTrace tailWord_5222908 prefixEnd_5222908 2681862218212956582130289 := by
  unfold tailWord_5222908
  simp only [CollatzResearch.WordTrace]
  refine ⟨95247552281151896257814689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126996736374869195010419585 95247552281151896257814689)
  ·
    refine ⟨71435664210863922193361017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95247552281151896257814689 71435664210863922193361017)
    ·
      refine ⟨53576748158147941645020763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71435664210863922193361017 53576748158147941645020763)
      ·
        refine ⟨80365122237221912467531145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53576748158147941645020763 80365122237221912467531145)
        ·
          refine ⟨60273841677916434350648359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80365122237221912467531145 60273841677916434350648359)
          ·
            refine ⟨90410762516874651525972539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60273841677916434350648359 90410762516874651525972539)
            ·
              refine ⟨135616143775311977288958809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90410762516874651525972539 135616143775311977288958809)
              ·
                refine ⟨101712107831483982966719107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 135616143775311977288958809 101712107831483982966719107)
                ·
                  refine ⟨152568161747225974450078661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101712107831483982966719107 152568161747225974450078661)
                  ·
                    refine ⟨28606530327604870209389749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 152568161747225974450078661 28606530327604870209389749)
                    ·
                      refine ⟨2681862218212956582130289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28606530327604870209389749 2681862218212956582130289)
                      ·
                        rfl

theorem cell23_5222908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_5222908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5222908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5222908 prefixEnd_5222908 := by exact prefixLift 5222908
  have htrace : WordTrace (prefixWord ++ tailWord_5222908) baseStart_5222908 baseEnd_5222908 := by
    simpa [prefixWord, tailWord_5222908, baseEnd_5222908] using wordTrace_append hprefix tailTrace_5222908
  have hstable : (prefixWord ++ tailWord_5222908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5222908).length < 2 ^ (prefixWord ++ tailWord_5222908).sum := by decide
  have hdescent : baseEnd_5222908 < baseStart_5222908 := by decide
  rcases family_descends (prefixWord ++ tailWord_5222908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5222922 : List Nat := [3, 1, 2, 2, 2, 1, 1, 3, 3, 3, 2]
def baseStart_5222922 : Nat := 118140960795 + 5222922 * 2 ^ 59
def prefixEnd_5222922 : Nat := 4983230072969 + 3 ^ 40 * 5222922 * 2
def baseEnd_5222922 : Nat := 2681869406942119527355225

theorem tailTrace_5222922 : CollatzResearch.WordTrace tailWord_5222922 prefixEnd_5222922 2681869406942119527355225 := by
  unfold tailWord_5222922
  simp only [CollatzResearch.WordTrace]
  refine ⟨47623903796063268226659755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 126997076789502048604426013 47623903796063268226659755)
  ·
    refine ⟨71435855694094902339989633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47623903796063268226659755 71435855694094902339989633)
    ·
      refine ⟨53576891770571176754992225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71435855694094902339989633 53576891770571176754992225)
      ·
        refine ⟨40182668827928382566244169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53576891770571176754992225 40182668827928382566244169)
        ·
          refine ⟨30137001620946286924683127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40182668827928382566244169 30137001620946286924683127)
          ·
            refine ⟨45205502431419430387024691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30137001620946286924683127 45205502431419430387024691)
            ·
              refine ⟨67808253647129145580537037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45205502431419430387024691 67808253647129145580537037)
              ·
                refine ⟨25428095117673429592701389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67808253647129145580537037 25428095117673429592701389)
                ·
                  refine ⟨9535535669127536097263021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25428095117673429592701389 9535535669127536097263021)
                  ·
                    refine ⟨3575825875922826036473633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9535535669127536097263021 3575825875922826036473633)
                    ·
                      refine ⟨2681869406942119527355225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3575825875922826036473633 2681869406942119527355225)
                      ·
                        rfl

theorem cell23_5222922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 3, 3, 2].length) (baseStart_5222922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5222922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5222922 prefixEnd_5222922 := by exact prefixLift 5222922
  have htrace : WordTrace (prefixWord ++ tailWord_5222922) baseStart_5222922 baseEnd_5222922 := by
    simpa [prefixWord, tailWord_5222922, baseEnd_5222922] using wordTrace_append hprefix tailTrace_5222922
  have hstable : (prefixWord ++ tailWord_5222922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5222922).length < 2 ^ (prefixWord ++ tailWord_5222922).sum := by decide
  have hdescent : baseEnd_5222922 < baseStart_5222922 := by decide
  rcases family_descends (prefixWord ++ tailWord_5222922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5222965 : List Nat := [1, 3, 3, 1, 1, 2, 1, 3, 2, 2, 4]
def baseStart_5222965 : Nat := 118140960795 + 5222965 * 2 ^ 59
def prefixEnd_5222965 : Nat := 4983230072969 + 3 ^ 40 * 5222965 * 2
def baseEnd_5222965 : Nat := 2681891486610262859117527

theorem tailTrace_5222965 : CollatzResearch.WordTrace tailWord_5222965 prefixEnd_5222965 2681891486610262859117527 := by
  unfold tailWord_5222965
  simp only [CollatzResearch.WordTrace]
  refine ⟨190497183523097291250454349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126998122348731527500302899 190497183523097291250454349)
  ·
    refine ⟨71436443821161484218920381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190497183523097291250454349 71436443821161484218920381)
    ·
      refine ⟨26788666432935556582095143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71436443821161484218920381 26788666432935556582095143)
      ·
        refine ⟨40182999649403334873142715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26788666432935556582095143 40182999649403334873142715)
        ·
          refine ⟨60274499474105002309714073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40182999649403334873142715 60274499474105002309714073)
          ·
            refine ⟨45205874605578751732285555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60274499474105002309714073 45205874605578751732285555)
            ·
              refine ⟨67808811908368127598428333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45205874605578751732285555 67808811908368127598428333)
              ·
                refine ⟨25428304465638047849410625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67808811908368127598428333 25428304465638047849410625)
                ·
                  refine ⟨19071228349228535887057969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25428304465638047849410625 19071228349228535887057969)
                  ·
                    refine ⟨14303421261921401915293477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19071228349228535887057969 14303421261921401915293477)
                    ·
                      refine ⟨2681891486610262859117527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14303421261921401915293477 2681891486610262859117527)
                      ·
                        rfl

theorem cell23_5222965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_5222965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5222965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5222965 prefixEnd_5222965 := by exact prefixLift 5222965
  have htrace : WordTrace (prefixWord ++ tailWord_5222965) baseStart_5222965 baseEnd_5222965 := by
    simpa [prefixWord, tailWord_5222965, baseEnd_5222965] using wordTrace_append hprefix tailTrace_5222965
  have hstable : (prefixWord ++ tailWord_5222965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5222965).length < 2 ^ (prefixWord ++ tailWord_5222965).sum := by decide
  have hdescent : baseEnd_5222965 < baseStart_5222965 := by decide
  rcases family_descends (prefixWord ++ tailWord_5222965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5223009 : List Nat := [1, 2, 3, 1, 1, 5, 3, 2, 5]
def baseStart_5223009 : Nat := 118140960795 + 5223009 * 2 ^ 59
def prefixEnd_5223009 : Nat := 4983230072969 + 3 ^ 40 * 5223009 * 2
def baseEnd_5223009 : Nat := 297990453306562298551925

theorem tailTrace_5223009 : CollatzResearch.WordTrace tailWord_5223009 prefixEnd_5223009 297990453306562298551925 := by
  unfold tailWord_5223009
  simp only [CollatzResearch.WordTrace]
  refine ⟨190498788334937886765056081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 126999192223291924510037387 190498788334937886765056081)
  ·
    refine ⟨142874091251203415073792061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190498788334937886765056081 142874091251203415073792061)
    ·
      refine ⟨53577784219201280652672023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142874091251203415073792061 53577784219201280652672023)
      ·
        refine ⟨80366676328801920979008035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53577784219201280652672023 80366676328801920979008035)
        ·
          refine ⟨120550014493202881468512053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80366676328801920979008035 120550014493202881468512053)
          ·
            refine ⟨11301563858737770137673005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 120550014493202881468512053 11301563858737770137673005)
            ·
              refine ⟨4238086447026663801627377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11301563858737770137673005 4238086447026663801627377)
              ·
                refine ⟨3178564835269997851220533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4238086447026663801627377 3178564835269997851220533)
                ·
                  refine ⟨297990453306562298551925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3178564835269997851220533 297990453306562298551925)
                  ·
                    rfl

theorem cell23_5223009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 3, 2, 5].length) (baseStart_5223009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5223009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5223009 prefixEnd_5223009 := by exact prefixLift 5223009
  have htrace : WordTrace (prefixWord ++ tailWord_5223009) baseStart_5223009 baseEnd_5223009 := by
    simpa [prefixWord, tailWord_5223009, baseEnd_5223009] using wordTrace_append hprefix tailTrace_5223009
  have hstable : (prefixWord ++ tailWord_5223009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5223009).length < 2 ^ (prefixWord ++ tailWord_5223009).sum := by decide
  have hdescent : baseEnd_5223009 < baseStart_5223009 := by decide
  rcases family_descends (prefixWord ++ tailWord_5223009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5223012 : List Nat := [2, 3, 1, 1, 2, 2, 2, 1, 2, 5, 2]
def baseStart_5223012 : Nat := 118140960795 + 5223012 * 2 ^ 59
def prefixEnd_5223012 : Nat := 4983230072969 + 3 ^ 40 * 5223012 * 2
def baseEnd_5223012 : Nat := 2681915620201024175229811

theorem tailTrace_5223012 : CollatzResearch.WordTrace tailWord_5223012 prefixEnd_5223012 2681915620201024175229811 := by
  unfold tailWord_5223012
  simp only [CollatzResearch.WordTrace]
  refine ⟨95249448876963509138707645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 126999265169284678851610193 95249448876963509138707645)
  ·
    refine ⟨35718543328861315927015367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95249448876963509138707645 35718543328861315927015367)
    ·
      refine ⟨53577814993291973890523051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35718543328861315927015367 53577814993291973890523051)
      ·
        refine ⟨80366722489937960835784577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53577814993291973890523051 80366722489937960835784577)
        ·
          refine ⟨60275041867453470626838433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80366722489937960835784577 60275041867453470626838433)
          ·
            refine ⟨45206281400590102970128825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60275041867453470626838433 45206281400590102970128825)
            ·
              refine ⟨33904711050442577227596619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45206281400590102970128825 33904711050442577227596619)
              ·
                refine ⟨50857066575663865841394929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33904711050442577227596619 50857066575663865841394929)
                ·
                  refine ⟨38142799931747899381046197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50857066575663865841394929 38142799931747899381046197)
                  ·
                    refine ⟨3575887493601365566973081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38142799931747899381046197 3575887493601365566973081)
                    ·
                      refine ⟨2681915620201024175229811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3575887493601365566973081 2681915620201024175229811)
                      ·
                        rfl

theorem cell23_5223012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 2, 5, 2].length) (baseStart_5223012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5223012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5223012 prefixEnd_5223012 := by exact prefixLift 5223012
  have htrace : WordTrace (prefixWord ++ tailWord_5223012) baseStart_5223012 baseEnd_5223012 := by
    simpa [prefixWord, tailWord_5223012, baseEnd_5223012] using wordTrace_append hprefix tailTrace_5223012
  have hstable : (prefixWord ++ tailWord_5223012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5223012).length < 2 ^ (prefixWord ++ tailWord_5223012).sum := by decide
  have hdescent : baseEnd_5223012 < baseStart_5223012 := by decide
  rcases family_descends (prefixWord ++ tailWord_5223012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5223086 : List Nat := [4, 1, 4, 1, 1, 2, 1, 2, 3, 4]
def baseStart_5223086 : Nat := 118140960795 + 5223086 * 2 ^ 59
def prefixEnd_5223086 : Nat := 4983230072969 + 3 ^ 40 * 5223086 * 2
def baseEnd_5223086 : Nat := 893984539256485628568157

theorem tailTrace_5223086 : CollatzResearch.WordTrace tailWord_5223086 prefixEnd_5223086 893984539256485628568157 := by
  unfold tailWord_5223086
  simp only [CollatzResearch.WordTrace]
  refine ⟨23812699594457366114451139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127001064503772619277072741 23812699594457366114451139)
  ·
    refine ⟨35719049391686049171676709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23812699594457366114451139 35719049391686049171676709)
    ·
      refine ⟨6697321760941134219689383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35719049391686049171676709 6697321760941134219689383)
      ·
        refine ⟨10045982641411701329534075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6697321760941134219689383 10045982641411701329534075)
        ·
          refine ⟨15068973962117551994301113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10045982641411701329534075 15068973962117551994301113)
          ·
            refine ⟨11301730471588163995725835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15068973962117551994301113 11301730471588163995725835)
            ·
              refine ⟨16952595707382245993588753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11301730471588163995725835 16952595707382245993588753)
              ·
                refine ⟨12714446780536684495191565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16952595707382245993588753 12714446780536684495191565)
                ·
                  refine ⟨4767917542701256685696837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12714446780536684495191565 4767917542701256685696837)
                  ·
                    refine ⟨893984539256485628568157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4767917542701256685696837 893984539256485628568157)
                    ·
                      rfl

theorem cell23_5223086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_5223086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5223086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5223086 prefixEnd_5223086 := by exact prefixLift 5223086
  have htrace : WordTrace (prefixWord ++ tailWord_5223086) baseStart_5223086 baseEnd_5223086 := by
    simpa [prefixWord, tailWord_5223086, baseEnd_5223086] using wordTrace_append hprefix tailTrace_5223086
  have hstable : (prefixWord ++ tailWord_5223086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5223086).length < 2 ^ (prefixWord ++ tailWord_5223086).sum := by decide
  have hdescent : baseEnd_5223086 < baseStart_5223086 := by decide
  rcases family_descends (prefixWord ++ tailWord_5223086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5223149 : List Nat := [1, 5, 1, 2, 1, 1, 1, 1, 2, 6, 2]
def baseStart_5223149 : Nat := 118140960795 + 5223149 * 2 ^ 59
def prefixEnd_5223149 : Nat := 4983230072969 + 3 ^ 40 * 5223149 * 2
def baseEnd_5223149 : Nat := 2681985967050690139216681

theorem tailTrace_5223149 : CollatzResearch.WordTrace tailWord_5223149 prefixEnd_5223149 2681985967050690139216681 := by
  unfold tailWord_5223149
  simp only [CollatzResearch.WordTrace]
  refine ⟨190503894554430690675152501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127002596369620460450101667 190503894554430690675152501)
  ·
    refine ⟨17859740114477877250795547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 190503894554430690675152501 17859740114477877250795547)
    ·
      refine ⟨26789610171716815876193321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17859740114477877250795547 26789610171716815876193321)
      ·
        refine ⟨20092207628787611907144991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26789610171716815876193321 20092207628787611907144991)
        ·
          refine ⟨30138311443181417860717487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20092207628787611907144991 30138311443181417860717487)
          ·
            refine ⟨45207467164772126791076231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30138311443181417860717487 45207467164772126791076231)
            ·
              refine ⟨67811200747158190186614347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45207467164772126791076231 67811200747158190186614347)
              ·
                refine ⟨101716801120737285279921521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67811200747158190186614347 101716801120737285279921521)
                ·
                  refine ⟨76287600840552963959941141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101716801120737285279921521 76287600840552963959941141)
                  ·
                    refine ⟨3575981289400920185622241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 76287600840552963959941141 3575981289400920185622241)
                    ·
                      refine ⟨2681985967050690139216681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3575981289400920185622241 2681985967050690139216681)
                      ·
                        rfl

theorem cell23_5223149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 6, 2].length) (baseStart_5223149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5223149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5223149 prefixEnd_5223149 := by exact prefixLift 5223149
  have htrace : WordTrace (prefixWord ++ tailWord_5223149) baseStart_5223149 baseEnd_5223149 := by
    simpa [prefixWord, tailWord_5223149, baseEnd_5223149] using wordTrace_append hprefix tailTrace_5223149
  have hstable : (prefixWord ++ tailWord_5223149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5223149).length < 2 ^ (prefixWord ++ tailWord_5223149).sum := by decide
  have hdescent : baseEnd_5223149 < baseStart_5223149 := by decide
  rcases family_descends (prefixWord ++ tailWord_5223149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5223162 : List Nat := [3, 1, 1, 1, 1, 3, 2, 4, 1, 2, 4]
def baseStart_5223162 : Nat := 118140960795 + 5223162 * 2 ^ 59
def prefixEnd_5223162 : Nat := 4983230072969 + 3 ^ 40 * 5223162 * 2
def baseEnd_5223162 : Nat := 2681992642299198588354121

theorem tailTrace_5223162 : CollatzResearch.WordTrace tailWord_5223162 prefixEnd_5223162 2681992642299198588354121 := by
  unfold tailWord_5223162
  simp only [CollatzResearch.WordTrace]
  refine ⟨47626092175845898473843935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127002912468922395930250493 47626092175845898473843935)
  ·
    refine ⟨71439138263768847710765903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47626092175845898473843935 71439138263768847710765903)
    ·
      refine ⟨107158707395653271566148855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71439138263768847710765903 107158707395653271566148855)
      ·
        refine ⟨160738061093479907349223283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107158707395653271566148855 160738061093479907349223283)
        ·
          refine ⟨241107091640219861023834925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160738061093479907349223283 241107091640219861023834925)
          ·
            refine ⟨90415159365082447883938097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 241107091640219861023834925 90415159365082447883938097)
            ·
              refine ⟨67811369523811835912953573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90415159365082447883938097 67811369523811835912953573)
              ·
                refine ⟨12714631785714719233678795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67811369523811835912953573 12714631785714719233678795)
                ·
                  refine ⟨19071947678572078850518193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12714631785714719233678795 19071947678572078850518193)
                  ·
                    refine ⟨14303960758929059137888645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19071947678572078850518193 14303960758929059137888645)
                    ·
                      refine ⟨2681992642299198588354121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14303960758929059137888645 2681992642299198588354121)
                      ·
                        rfl

theorem cell23_5223162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 4, 1, 2, 4].length) (baseStart_5223162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5223162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5223162 prefixEnd_5223162 := by exact prefixLift 5223162
  have htrace : WordTrace (prefixWord ++ tailWord_5223162) baseStart_5223162 baseEnd_5223162 := by
    simpa [prefixWord, tailWord_5223162, baseEnd_5223162] using wordTrace_append hprefix tailTrace_5223162
  have hstable : (prefixWord ++ tailWord_5223162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5223162).length < 2 ^ (prefixWord ++ tailWord_5223162).sum := by decide
  have hdescent : baseEnd_5223162 < baseStart_5223162 := by decide
  rcases family_descends (prefixWord ++ tailWord_5223162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5223166 : List Nat := [4, 2, 2, 1, 2, 1, 2, 3, 1, 1, 4]
def baseStart_5223166 : Nat := 118140960795 + 5223166 * 2 ^ 59
def prefixEnd_5223166 : Nat := 4983230072969 + 3 ^ 40 * 5223166 * 2
def baseEnd_5223166 : Nat := 2681994696221816572704103

theorem tailTrace_5223166 : CollatzResearch.WordTrace tailWord_5223166 prefixEnd_5223166 2681994696221816572704103 := by
  unfold tailWord_5223166
  simp only [CollatzResearch.WordTrace]
  refine ⟨23813064324421137822315169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127003009730246068385680901 23813064324421137822315169)
  ·
    refine ⟨17859798243315853366736377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23813064324421137822315169 17859798243315853366736377)
    ·
      refine ⟨13394848682486890025052283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17859798243315853366736377 13394848682486890025052283)
      ·
        refine ⟨20092273023730335037578425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13394848682486890025052283 20092273023730335037578425)
        ·
          refine ⟨15069204767797751278183819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20092273023730335037578425 15069204767797751278183819)
          ·
            refine ⟨22603807151696626917275729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15069204767797751278183819 22603807151696626917275729)
            ·
              refine ⟨16952855363772470187956797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22603807151696626917275729 16952855363772470187956797)
              ·
                refine ⟨6357320761414676320483799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16952855363772470187956797 6357320761414676320483799)
                ·
                  refine ⟨9535981142122014480725699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6357320761414676320483799 9535981142122014480725699)
                  ·
                    refine ⟨14303971713183021721088549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9535981142122014480725699 14303971713183021721088549)
                    ·
                      refine ⟨2681994696221816572704103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14303971713183021721088549 2681994696221816572704103)
                      ·
                        rfl

theorem cell23_5223166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_5223166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5223166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5223166 prefixEnd_5223166 := by exact prefixLift 5223166
  have htrace : WordTrace (prefixWord ++ tailWord_5223166) baseStart_5223166 baseEnd_5223166 := by
    simpa [prefixWord, tailWord_5223166, baseEnd_5223166] using wordTrace_append hprefix tailTrace_5223166
  have hstable : (prefixWord ++ tailWord_5223166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5223166).length < 2 ^ (prefixWord ++ tailWord_5223166).sum := by decide
  have hdescent : baseEnd_5223166 < baseStart_5223166 := by decide
  rcases family_descends (prefixWord ++ tailWord_5223166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5223209 : List Nat := [1, 2, 1, 1, 1, 1, 1, 7, 3, 3, 2]
def baseStart_5223209 : Nat := 118140960795 + 5223209 * 2 ^ 59
def prefixEnd_5223209 : Nat := 4983230072969 + 3 ^ 40 * 5223209 * 2
def baseEnd_5223209 : Nat := 2682016775889959904466405

theorem tailTrace_5223209 : CollatzResearch.WordTrace tailWord_5223209 prefixEnd_5223209 2682016775889959904466405 := by
  unfold tailWord_5223209
  simp only [CollatzResearch.WordTrace]
  refine ⟨190506082934213320922336681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127004055289475547281557787 190506082934213320922336681)
  ·
    refine ⟨142879562200659990691752511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190506082934213320922336681 142879562200659990691752511)
    ·
      refine ⟨214319343300989986037628767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142879562200659990691752511 214319343300989986037628767)
      ·
        refine ⟨321479014951484979056443151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214319343300989986037628767 321479014951484979056443151)
        ·
          refine ⟨482218522427227468584664727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 321479014951484979056443151 482218522427227468584664727)
          ·
            refine ⟨723327783640841202876997091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 482218522427227468584664727 723327783640841202876997091)
            ·
              refine ⟨1084991675461261804315495637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 723327783640841202876997091 1084991675461261804315495637)
              ·
                refine ⟨25429492393623323538644429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1084991675461261804315495637 25429492393623323538644429)
                ·
                  refine ⟨9536059647608746326991661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25429492393623323538644429 9536059647608746326991661)
                  ·
                    refine ⟨3576022367853279872621873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9536059647608746326991661 3576022367853279872621873)
                    ·
                      refine ⟨2682016775889959904466405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3576022367853279872621873 2682016775889959904466405)
                      ·
                        rfl

theorem cell23_5223209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 3, 3, 2].length) (baseStart_5223209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5223209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5223209 prefixEnd_5223209 := by exact prefixLift 5223209
  have htrace : WordTrace (prefixWord ++ tailWord_5223209) baseStart_5223209 baseEnd_5223209 := by
    simpa [prefixWord, tailWord_5223209, baseEnd_5223209] using wordTrace_append hprefix tailTrace_5223209
  have hstable : (prefixWord ++ tailWord_5223209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5223209).length < 2 ^ (prefixWord ++ tailWord_5223209).sum := by decide
  have hdescent : baseEnd_5223209 < baseStart_5223209 := by decide
  rcases family_descends (prefixWord ++ tailWord_5223209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5223213 : List Nat := [1, 5, 3, 2, 1, 1, 1, 2, 1, 2, 4]
def baseStart_5223213 : Nat := 118140960795 + 5223213 * 2 ^ 59
def prefixEnd_5223213 : Nat := 4983230072969 + 3 ^ 40 * 5223213 * 2
def baseEnd_5223213 : Nat := 2682018829812577888816387

theorem tailTrace_5223213 : CollatzResearch.WordTrace tailWord_5223213 prefixEnd_5223213 2682018829812577888816387 := by
  unfold tailWord_5223213
  simp only [CollatzResearch.WordTrace]
  refine ⟨190506228826198829605482293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127004152550799219736988195 190506228826198829605482293)
  ·
    refine ⟨17859958952456140275513965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 190506228826198829605482293 17859958952456140275513965)
    ·
      refine ⟨6697484607171052603317737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17859958952456140275513965 6697484607171052603317737)
      ·
        refine ⟨5023113455378289452488303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6697484607171052603317737 5023113455378289452488303)
        ·
          refine ⟨7534670183067434178732455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5023113455378289452488303 7534670183067434178732455)
          ·
            refine ⟨11302005274601151268098683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7534670183067434178732455 11302005274601151268098683)
            ·
              refine ⟨16953007911901726902148025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11302005274601151268098683 16953007911901726902148025)
              ·
                refine ⟨12714755933926295176611019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16953007911901726902148025 12714755933926295176611019)
                ·
                  refine ⟨19072133900889442764916529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12714755933926295176611019 19072133900889442764916529)
                  ·
                    refine ⟨14304100425667082073687397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19072133900889442764916529 14304100425667082073687397)
                    ·
                      refine ⟨2682018829812577888816387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14304100425667082073687397 2682018829812577888816387)
                      ·
                        rfl

theorem cell23_5223213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_5223213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5223213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5223213 prefixEnd_5223213 := by exact prefixLift 5223213
  have htrace : WordTrace (prefixWord ++ tailWord_5223213) baseStart_5223213 baseEnd_5223213 := by
    simpa [prefixWord, tailWord_5223213, baseEnd_5223213] using wordTrace_append hprefix tailTrace_5223213
  have hstable : (prefixWord ++ tailWord_5223213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5223213).length < 2 ^ (prefixWord ++ tailWord_5223213).sum := by decide
  have hdescent : baseEnd_5223213 < baseStart_5223213 := by decide
  rcases family_descends (prefixWord ++ tailWord_5223213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5223220 : List Nat := [2, 5, 1, 1, 3, 1, 3, 1, 1, 2, 3]
def baseStart_5223220 : Nat := 118140960795 + 5223220 * 2 ^ 59
def prefixEnd_5223220 : Nat := 4983230072969 + 3 ^ 40 * 5223220 * 2
def baseEnd_5223220 : Nat := 2682022424177159361428855

theorem tailTrace_5223220 : CollatzResearch.WordTrace tailWord_5223220 prefixEnd_5223220 2682022424177159361428855 := by
  unfold tailWord_5223220
  simp only [CollatzResearch.WordTrace]
  refine ⟨95253242068586734900493557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127004322758115646533991409 95253242068586734900493557)
  ·
    refine ⟨8929991443930006396921271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 95253242068586734900493557 8929991443930006396921271)
    ·
      refine ⟨13394987165895009595381907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8929991443930006396921271 13394987165895009595381907)
      ·
        refine ⟨20092480748842514393072861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13394987165895009595381907 20092480748842514393072861)
        ·
          refine ⟨7534680280815942897402323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20092480748842514393072861 7534680280815942897402323)
          ·
            refine ⟨11302020421223914346103485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7534680280815942897402323 11302020421223914346103485)
            ·
              refine ⟨4238257657958967879788807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11302020421223914346103485 4238257657958967879788807)
              ·
                refine ⟨6357386486938451819683211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4238257657958967879788807 6357386486938451819683211)
                ·
                  refine ⟨9536079730407677729524817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6357386486938451819683211 9536079730407677729524817)
                  ·
                    refine ⟨7152059797805758297143613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9536079730407677729524817 7152059797805758297143613)
                    ·
                      refine ⟨2682022424177159361428855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7152059797805758297143613 2682022424177159361428855)
                      ·
                        rfl

theorem cell23_5223220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 3, 1, 1, 2, 3].length) (baseStart_5223220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5223220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5223220 prefixEnd_5223220 := by exact prefixLift 5223220
  have htrace : WordTrace (prefixWord ++ tailWord_5223220) baseStart_5223220 baseEnd_5223220 := by
    simpa [prefixWord, tailWord_5223220, baseEnd_5223220] using wordTrace_append hprefix tailTrace_5223220
  have hstable : (prefixWord ++ tailWord_5223220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5223220).length < 2 ^ (prefixWord ++ tailWord_5223220).sum := by decide
  have hdescent : baseEnd_5223220 < baseStart_5223220 := by decide
  rcases family_descends (prefixWord ++ tailWord_5223220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5223239 : List Nat := [1, 1, 4, 1, 2, 1, 1, 1, 5, 4, 2]
def baseStart_5223239 : Nat := 118140960795 + 5223239 * 2 ^ 59
def prefixEnd_5223239 : Nat := 4983230072969 + 3 ^ 40 * 5223239 * 2
def baseEnd_5223239 : Nat := 2682032180309594787091267

theorem tailTrace_5223239 : CollatzResearch.WordTrace tailWord_5223239 prefixEnd_5223239 2682032180309594787091267 := by
  unfold tailWord_5223239
  simp only [CollatzResearch.WordTrace]
  refine ⟨190507177124104636045928771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127004784749403090697285847 190507177124104636045928771)
  ·
    refine ⟨285760765686156954068893157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190507177124104636045928771 285760765686156954068893157)
    ·
      refine ⟨53580143566154428887917467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 285760765686156954068893157 53580143566154428887917467)
      ·
        refine ⟨80370215349231643331876201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53580143566154428887917467 80370215349231643331876201)
        ·
          refine ⟨60277661511923732498907151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80370215349231643331876201 60277661511923732498907151)
          ·
            refine ⟨90416492267885598748360727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60277661511923732498907151 90416492267885598748360727)
            ·
              refine ⟨135624738401828398122541091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90416492267885598748360727 135624738401828398122541091)
              ·
                refine ⟨203437107602742597183811637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135624738401828398122541091 203437107602742597183811637)
                ·
                  refine ⟨19072228837757118485982341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 203437107602742597183811637 19072228837757118485982341)
                  ·
                    refine ⟨3576042907079459716121689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19072228837757118485982341 3576042907079459716121689)
                    ·
                      refine ⟨2682032180309594787091267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3576042907079459716121689 2682032180309594787091267)
                      ·
                        rfl

theorem cell23_5223239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 5, 4, 2].length) (baseStart_5223239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5223239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5223239 prefixEnd_5223239 := by exact prefixLift 5223239
  have htrace : WordTrace (prefixWord ++ tailWord_5223239) baseStart_5223239 baseEnd_5223239 := by
    simpa [prefixWord, tailWord_5223239, baseEnd_5223239] using wordTrace_append hprefix tailTrace_5223239
  have hstable : (prefixWord ++ tailWord_5223239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5223239).length < 2 ^ (prefixWord ++ tailWord_5223239).sum := by decide
  have hdescent : baseEnd_5223239 < baseStart_5223239 := by decide
  rcases family_descends (prefixWord ++ tailWord_5223239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5223242 : List Nat := [3, 1, 2, 1, 1, 1, 2, 2, 4, 1, 5]
def baseStart_5223242 : Nat := 118140960795 + 5223242 * 2 ^ 59
def prefixEnd_5223242 : Nat := 4983230072969 + 3 ^ 40 * 5223242 * 2
def baseEnd_5223242 : Nat := 2682033720751558275353753

theorem tailTrace_5223242 : CollatzResearch.WordTrace tailWord_5223242 prefixEnd_5223242 2682033720751558275353753 := by
  unfold tailWord_5223242
  simp only [CollatzResearch.WordTrace]
  refine ⟨47626821635773441889571995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127004857695395845038858653 47626821635773441889571995)
  ·
    refine ⟨71440232453660162834357993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47626821635773441889571995 71440232453660162834357993)
    ·
      refine ⟨53580174340245122125768495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71440232453660162834357993 53580174340245122125768495)
      ·
        refine ⟨80370261510367683188652743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53580174340245122125768495 80370261510367683188652743)
        ·
          refine ⟨120555392265551524782979115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80370261510367683188652743 120555392265551524782979115)
          ·
            refine ⟨180833088398327287174468673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120555392265551524782979115 180833088398327287174468673)
            ·
              refine ⟨135624816298745465380851505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 180833088398327287174468673 135624816298745465380851505)
              ·
                refine ⟨101718612224059099035638629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 135624816298745465380851505 101718612224059099035638629)
                ·
                  refine ⟨19072239792011081069182243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 101718612224059099035638629 19072239792011081069182243)
                  ·
                    refine ⟨28608359688016621603773365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19072239792011081069182243 28608359688016621603773365)
                    ·
                      refine ⟨2682033720751558275353753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28608359688016621603773365 2682033720751558275353753)
                      ·
                        rfl

theorem cell23_5223242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 4, 1, 5].length) (baseStart_5223242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5223242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5223242 prefixEnd_5223242 := by exact prefixLift 5223242
  have htrace : WordTrace (prefixWord ++ tailWord_5223242) baseStart_5223242 baseEnd_5223242 := by
    simpa [prefixWord, tailWord_5223242, baseEnd_5223242] using wordTrace_append hprefix tailTrace_5223242
  have hstable : (prefixWord ++ tailWord_5223242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5223242).length < 2 ^ (prefixWord ++ tailWord_5223242).sum := by decide
  have hdescent : baseEnd_5223242 < baseStart_5223242 := by decide
  rcases family_descends (prefixWord ++ tailWord_5223242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5223249 : List Nat := [1, 2, 2, 1, 6, 1, 1, 1, 2, 6]
def baseStart_5223249 : Nat := 118140960795 + 5223249 * 2 ^ 59
def prefixEnd_5223249 : Nat := 4983230072969 + 3 ^ 40 * 5223249 * 2
def baseEnd_5223249 : Nat := 894012438372046582655407

theorem tailTrace_5223249 : CollatzResearch.WordTrace tailWord_5223249 prefixEnd_5223249 894012438372046582655407 := by
  unfold tailWord_5223249
  simp only [CollatzResearch.WordTrace]
  refine ⟨190507541854068407753792801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127005027902712271835861867 190507541854068407753792801)
  ·
    refine ⟨142880656390551305815344601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190507541854068407753792801 142880656390551305815344601)
    ·
      refine ⟨107160492292913479361508451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142880656390551305815344601 107160492292913479361508451)
      ·
        refine ⟨160740738439370219042262677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107160492292913479361508451 160740738439370219042262677)
        ·
          refine ⟨7534722114345479017606063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 160740738439370219042262677 7534722114345479017606063)
          ·
            refine ⟨11302083171518218526409095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7534722114345479017606063 11302083171518218526409095)
            ·
              refine ⟨16953124757277327789613643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11302083171518218526409095 16953124757277327789613643)
              ·
                refine ⟨25429687135915991684420465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16953124757277327789613643 25429687135915991684420465)
                ·
                  refine ⟨19072265351936993763315349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25429687135915991684420465 19072265351936993763315349)
                  ·
                    refine ⟨894012438372046582655407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19072265351936993763315349 894012438372046582655407)
                    ·
                      rfl

theorem cell23_5223249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 2, 6].length) (baseStart_5223249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5223249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5223249 prefixEnd_5223249 := by exact prefixLift 5223249
  have htrace : WordTrace (prefixWord ++ tailWord_5223249) baseStart_5223249 baseEnd_5223249 := by
    simpa [prefixWord, tailWord_5223249, baseEnd_5223249] using wordTrace_append hprefix tailTrace_5223249
  have hstable : (prefixWord ++ tailWord_5223249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5223249).length < 2 ^ (prefixWord ++ tailWord_5223249).sum := by decide
  have hdescent : baseEnd_5223249 < baseStart_5223249 := by decide
  rcases family_descends (prefixWord ++ tailWord_5223249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5223286 : List Nat := [5, 1, 1, 3, 1, 1, 1, 2, 2, 2, 4]
def baseStart_5223286 : Nat := 118140960795 + 5223286 * 2 ^ 59
def prefixEnd_5223286 : Nat := 4983230072969 + 3 ^ 40 * 5223286 * 2
def baseEnd_5223286 : Nat := 2682056313900356103203551

theorem tailTrace_5223286 : CollatzResearch.WordTrace tailWord_5223286 prefixEnd_5223286 2682056313900356103203551 := by
  unfold tailWord_5223286
  simp only [CollatzResearch.WordTrace]
  refine ⟨11906805709683397692055607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 127005927569956242048593141 11906805709683397692055607)
  ·
    refine ⟨17860208564525096538083411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11906805709683397692055607 17860208564525096538083411)
    ·
      refine ⟨26790312846787644807125117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17860208564525096538083411 26790312846787644807125117)
      ·
        refine ⟨10046367317545366802671919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26790312846787644807125117 10046367317545366802671919)
        ·
          refine ⟨15069550976318050204007879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10046367317545366802671919 15069550976318050204007879)
          ·
            refine ⟨22604326464477075306011819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15069550976318050204007879 22604326464477075306011819)
            ·
              refine ⟨33906489696715612959017729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22604326464477075306011819 33906489696715612959017729)
              ·
                refine ⟨25429867272536709719263297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33906489696715612959017729 25429867272536709719263297)
                ·
                  refine ⟨19072400454402532289447473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25429867272536709719263297 19072400454402532289447473)
                  ·
                    refine ⟨14304300340801899217085605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19072400454402532289447473 14304300340801899217085605)
                    ·
                      refine ⟨2682056313900356103203551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14304300340801899217085605 2682056313900356103203551)
                      ·
                        rfl

theorem cell23_5223286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_5223286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5223286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5223286 prefixEnd_5223286 := by exact prefixLift 5223286
  have htrace : WordTrace (prefixWord ++ tailWord_5223286) baseStart_5223286 baseEnd_5223286 := by
    simpa [prefixWord, tailWord_5223286, baseEnd_5223286] using wordTrace_append hprefix tailTrace_5223286
  have hstable : (prefixWord ++ tailWord_5223286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5223286).length < 2 ^ (prefixWord ++ tailWord_5223286).sum := by decide
  have hdescent : baseEnd_5223286 < baseStart_5223286 := by decide
  rcases family_descends (prefixWord ++ tailWord_5223286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5223289 : List Nat := [1, 2, 1, 3, 2, 3, 1, 2, 2, 3, 3]
def baseStart_5223289 : Nat := 118140960795 + 5223289 * 2 ^ 59
def prefixEnd_5223289 : Nat := 4983230072969 + 3 ^ 40 * 5223289 * 2
def baseEnd_5223289 : Nat := 2682057854342319591466037

theorem tailTrace_5223289 : CollatzResearch.WordTrace tailWord_5223289 prefixEnd_5223289 2682057854342319591466037 := by
  unfold tailWord_5223289
  simp only [CollatzResearch.WordTrace]
  refine ⟨190509000773923494585248921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127006000515948996390165947 190509000773923494585248921)
  ·
    refine ⟨142881750580442620938936691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190509000773923494585248921 142881750580442620938936691)
    ·
      refine ⟨214322625870663931408405037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142881750580442620938936691 214322625870663931408405037)
      ·
        refine ⟨80370984701498974278151889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 214322625870663931408405037 80370984701498974278151889)
        ·
          refine ⟨60278238526124230708613917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80370984701498974278151889 60278238526124230708613917)
          ·
            refine ⟨22604339447296586515730219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60278238526124230708613917 22604339447296586515730219)
            ·
              refine ⟨33906509170944879773595329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22604339447296586515730219 33906509170944879773595329)
              ·
                refine ⟨25429881878208659830196497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33906509170944879773595329 25429881878208659830196497)
                ·
                  refine ⟨19072411408656494872647373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25429881878208659830196497 19072411408656494872647373)
                  ·
                    refine ⟨7152154278246185577242765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19072411408656494872647373 7152154278246185577242765)
                    ·
                      refine ⟨2682057854342319591466037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7152154278246185577242765 2682057854342319591466037)
                      ·
                        rfl

theorem cell23_5223289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 2, 3, 3].length) (baseStart_5223289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5223289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5223289 prefixEnd_5223289 := by exact prefixLift 5223289
  have htrace : WordTrace (prefixWord ++ tailWord_5223289) baseStart_5223289 baseEnd_5223289 := by
    simpa [prefixWord, tailWord_5223289, baseEnd_5223289] using wordTrace_append hprefix tailTrace_5223289
  have hstable : (prefixWord ++ tailWord_5223289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5223289).length < 2 ^ (prefixWord ++ tailWord_5223289).sum := by decide
  have hdescent : baseEnd_5223289 < baseStart_5223289 := by decide
  rcases family_descends (prefixWord ++ tailWord_5223289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5223306 : List Nat := [3, 1, 2, 4, 1, 1, 2, 1, 2, 3, 3]
def baseStart_5223306 : Nat := 118140960795 + 5223306 * 2 ^ 59
def prefixEnd_5223306 : Nat := 4983230072969 + 3 ^ 40 * 5223306 * 2
def baseEnd_5223306 : Nat := 2682066583513446024953459

theorem tailTrace_5223306 : CollatzResearch.WordTrace tailWord_5223306 prefixEnd_5223306 2682066583513446024953459 := by
  unfold tailWord_5223306
  simp only [CollatzResearch.WordTrace]
  refine ⟨47627405203715476622154443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127006413876574604325745181 47627405203715476622154443)
  ·
    refine ⟨71441107805573214933231665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47627405203715476622154443 71441107805573214933231665)
    ·
      refine ⟨53580830854179911199923749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71441107805573214933231665 53580830854179911199923749)
      ·
        refine ⟨10046405785158733349985703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53580830854179911199923749 10046405785158733349985703)
        ·
          refine ⟨15069608677738100024978555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10046405785158733349985703 15069608677738100024978555)
          ·
            refine ⟨22604413016607150037467833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15069608677738100024978555 22604413016607150037467833)
            ·
              refine ⟨16953309762455362528100875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22604413016607150037467833 16953309762455362528100875)
              ·
                refine ⟨25429964643683043792151313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16953309762455362528100875 25429964643683043792151313)
                ·
                  refine ⟨19072473482762282844113485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25429964643683043792151313 19072473482762282844113485)
                  ·
                    refine ⟨7152177556035856066542557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19072473482762282844113485 7152177556035856066542557)
                    ·
                      refine ⟨2682066583513446024953459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7152177556035856066542557 2682066583513446024953459)
                      ·
                        rfl

theorem cell23_5223306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_5223306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5223306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5223306 prefixEnd_5223306 := by exact prefixLift 5223306
  have htrace : WordTrace (prefixWord ++ tailWord_5223306) baseStart_5223306 baseEnd_5223306 := by
    simpa [prefixWord, tailWord_5223306, baseEnd_5223306] using wordTrace_append hprefix tailTrace_5223306
  have hstable : (prefixWord ++ tailWord_5223306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5223306).length < 2 ^ (prefixWord ++ tailWord_5223306).sum := by decide
  have hdescent : baseEnd_5223306 < baseStart_5223306 := by decide
  rcases family_descends (prefixWord ++ tailWord_5223306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5223396 : List Nat := [2, 3, 1, 1, 1, 1, 2, 1, 7, 1, 3]
def baseStart_5223396 : Nat := 118140960795 + 5223396 * 2 ^ 59
def prefixEnd_5223396 : Nat := 4983230072969 + 3 ^ 40 * 5223396 * 2
def baseEnd_5223396 : Nat := 2682112796772350672828045

theorem tailTrace_5223396 : CollatzResearch.WordTrace tailWord_5223396 prefixEnd_5223396 2682112796772350672828045 := by
  unfold tailWord_5223396
  simp only [CollatzResearch.WordTrace]
  refine ⟨95256451692267925929697021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127008602256357234572929361 95256451692267925929697021)
  ·
    refine ⟨35721169384600472223636383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95256451692267925929697021 35721169384600472223636383)
    ·
      refine ⟨53581754076900708335454575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35721169384600472223636383 53581754076900708335454575)
      ·
        refine ⟨80372631115351062503181863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53581754076900708335454575 80372631115351062503181863)
        ·
          refine ⟨120558946673026593754772795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80372631115351062503181863 120558946673026593754772795)
          ·
            refine ⟨180838420009539890632159193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120558946673026593754772795 180838420009539890632159193)
            ·
              refine ⟨135628815007154917974119395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 180838420009539890632159193 135628815007154917974119395)
              ·
                refine ⟨203443222510732376961179093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135628815007154917974119395 203443222510732376961179093)
                ·
                  refine ⟨4768200527595290085027635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 203443222510732376961179093 4768200527595290085027635)
                  ·
                    refine ⟨7152300791392935127541453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4768200527595290085027635 7152300791392935127541453)
                    ·
                      refine ⟨2682112796772350672828045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7152300791392935127541453 2682112796772350672828045)
                      ·
                        rfl

theorem cell23_5223396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 7, 1, 3].length) (baseStart_5223396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5223396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5223396 prefixEnd_5223396 := by exact prefixLift 5223396
  have htrace : WordTrace (prefixWord ++ tailWord_5223396) baseStart_5223396 baseEnd_5223396 := by
    simpa [prefixWord, tailWord_5223396, baseEnd_5223396] using wordTrace_append hprefix tailTrace_5223396
  have hstable : (prefixWord ++ tailWord_5223396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5223396).length < 2 ^ (prefixWord ++ tailWord_5223396).sum := by decide
  have hdescent : baseEnd_5223396 < baseStart_5223396 := by decide
  rcases family_descends (prefixWord ++ tailWord_5223396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5223436 : List Nat := [2, 2, 1, 2, 3, 2, 2, 1, 3, 1, 4]
def baseStart_5223436 : Nat := 118140960795 + 5223436 * 2 ^ 59
def prefixEnd_5223436 : Nat := 4983230072969 + 3 ^ 40 * 5223436 * 2
def baseEnd_5223436 : Nat := 2682133335998530516327861

theorem tailTrace_5223436 : CollatzResearch.WordTrace tailWord_5223436 prefixEnd_5223436 2682133335998530516327861 := by
  unfold tailWord_5223436
  simp only [CollatzResearch.WordTrace]
  refine ⟨95257181152195469345425081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127009574869593959127233441 95257181152195469345425081)
  ·
    refine ⟨71442885864146602009068811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95257181152195469345425081 71442885864146602009068811)
    ·
      refine ⟨107164328796219903013603217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71442885864146602009068811 107164328796219903013603217)
      ·
        refine ⟨80373246597164927260202413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107164328796219903013603217 80373246597164927260202413)
        ·
          refine ⟨30139967473936847722575905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80373246597164927260202413 30139967473936847722575905)
          ·
            refine ⟨22604975605452635791931929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30139967473936847722575905 22604975605452635791931929)
            ·
              refine ⟨16953731704089476843948947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22604975605452635791931929 16953731704089476843948947)
              ·
                refine ⟨25430597556134215265923421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16953731704089476843948947 25430597556134215265923421)
                ·
                  refine ⟨9536474083550330724721283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25430597556134215265923421 9536474083550330724721283)
                  ·
                    refine ⟨14304711125325496087081925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9536474083550330724721283 14304711125325496087081925)
                    ·
                      refine ⟨2682133335998530516327861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14304711125325496087081925 2682133335998530516327861)
                      ·
                        rfl

theorem cell23_5223436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 3, 1, 4].length) (baseStart_5223436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5223436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5223436 prefixEnd_5223436 := by exact prefixLift 5223436
  have htrace : WordTrace (prefixWord ++ tailWord_5223436) baseStart_5223436 baseEnd_5223436 := by
    simpa [prefixWord, tailWord_5223436, baseEnd_5223436] using wordTrace_append hprefix tailTrace_5223436
  have hstable : (prefixWord ++ tailWord_5223436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5223436).length < 2 ^ (prefixWord ++ tailWord_5223436).sum := by decide
  have hdescent : baseEnd_5223436 < baseStart_5223436 := by decide
  rcases family_descends (prefixWord ++ tailWord_5223436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5223439 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 4, 6, 3]
def baseStart_5223439 : Nat := 118140960795 + 5223439 * 2 ^ 59
def prefixEnd_5223439 : Nat := 4983230072969 + 3 ^ 40 * 5223439 * 2
def baseEnd_5223439 : Nat := 2682134876440494004590347

theorem tailTrace_5223439 : CollatzResearch.WordTrace tailWord_5223439 prefixEnd_5223439 2682134876440494004590347 := by
  unfold tailWord_5223439
  simp only [CollatzResearch.WordTrace]
  refine ⟨190514471723380070203209371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127009647815586713468806247 190514471723380070203209371)
  ·
    refine ⟨285771707585070105304814057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190514471723380070203209371 285771707585070105304814057)
    ·
      refine ⟨214328780688802578978610543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 285771707585070105304814057 214328780688802578978610543)
      ·
        refine ⟨321493171033203868467915815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214328780688802578978610543 321493171033203868467915815)
        ·
          refine ⟨482239756549805802701873723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 321493171033203868467915815 482239756549805802701873723)
          ·
            refine ⟨723359634824708704052810585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 482239756549805802701873723 723359634824708704052810585)
            ·
              refine ⟨542519726118531528039607939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 723359634824708704052810585 542519726118531528039607939)
              ·
                refine ⟨813779589177797292059411909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 542519726118531528039607939 813779589177797292059411909)
                ·
                  refine ⟨152583672970836992261139733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 813779589177797292059411909 152583672970836992261139733)
                  ·
                    refine ⟨7152359670507984012240925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 152583672970836992261139733 7152359670507984012240925)
                    ·
                      refine ⟨2682134876440494004590347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7152359670507984012240925 2682134876440494004590347)
                      ·
                        rfl

theorem cell23_5223439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 6, 3].length) (baseStart_5223439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5223439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5223439 prefixEnd_5223439 := by exact prefixLift 5223439
  have htrace : WordTrace (prefixWord ++ tailWord_5223439) baseStart_5223439 baseEnd_5223439 := by
    simpa [prefixWord, tailWord_5223439, baseEnd_5223439] using wordTrace_append hprefix tailTrace_5223439
  have hstable : (prefixWord ++ tailWord_5223439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5223439).length < 2 ^ (prefixWord ++ tailWord_5223439).sum := by decide
  have hdescent : baseEnd_5223439 < baseStart_5223439 := by decide
  rcases family_descends (prefixWord ++ tailWord_5223439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5223447 : List Nat := [1, 1, 3, 5, 1, 2, 2, 3, 1, 1, 3]
def baseStart_5223447 : Nat := 118140960795 + 5223447 * 2 ^ 59
def prefixEnd_5223447 : Nat := 4983230072969 + 3 ^ 40 * 5223447 * 2
def baseEnd_5223447 : Nat := 2682138984285729973290311

theorem tailTrace_5223447 : CollatzResearch.WordTrace tailWord_5223447 prefixEnd_5223447 2682138984285729973290311 := by
  unfold tailWord_5223447
  simp only [CollatzResearch.WordTrace]
  refine ⟨190514763507351087569500595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127009842338234058379667063 190514763507351087569500595)
  ·
    refine ⟨285772145261026631354250893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190514763507351087569500595 285772145261026631354250893)
    ·
      refine ⟨107164554472884986757844085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 285772145261026631354250893 107164554472884986757844085)
      ·
        refine ⟨10046676981832967508547883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 107164554472884986757844085 10046676981832967508547883)
        ·
          refine ⟨15070015472749451262821825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10046676981832967508547883 15070015472749451262821825)
          ·
            refine ⟨11302511604562088447116369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15070015472749451262821825 11302511604562088447116369)
            ·
              refine ⟨8476883703421566335337277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11302511604562088447116369 8476883703421566335337277)
              ·
                refine ⟨3178831388783087375751479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8476883703421566335337277 3178831388783087375751479)
                ·
                  refine ⟨4768247083174631063627219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3178831388783087375751479 4768247083174631063627219)
                  ·
                    refine ⟨7152370624761946595440829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4768247083174631063627219 7152370624761946595440829)
                    ·
                      refine ⟨2682138984285729973290311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7152370624761946595440829 2682138984285729973290311)
                      ·
                        rfl

theorem cell23_5223447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_5223447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5223447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5223447 prefixEnd_5223447 := by exact prefixLift 5223447
  have htrace : WordTrace (prefixWord ++ tailWord_5223447) baseStart_5223447 baseEnd_5223447 := by
    simpa [prefixWord, tailWord_5223447, baseEnd_5223447] using wordTrace_append hprefix tailTrace_5223447
  have hstable : (prefixWord ++ tailWord_5223447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5223447).length < 2 ^ (prefixWord ++ tailWord_5223447).sum := by decide
  have hdescent : baseEnd_5223447 < baseStart_5223447 := by decide
  rcases family_descends (prefixWord ++ tailWord_5223447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5223459 : List Nat := [1, 1, 1, 4, 3, 3, 10]
def baseStart_5223459 : Nat := 118140960795 + 5223459 * 2 ^ 59
def prefixEnd_5223459 : Nat := 4983230072969 + 3 ^ 40 * 5223459 * 2
def baseEnd_5223459 : Nat := 33112903037698566991855

theorem tailTrace_5223459 : CollatzResearch.WordTrace tailWord_5223459 prefixEnd_5223459 33112903037698566991855 := by
  unfold tailWord_5223459
  simp only [CollatzResearch.WordTrace]
  refine ⟨190515201183307613618937431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127010134122205075745958287 190515201183307613618937431)
  ·
    refine ⟨285772801774961420428406147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190515201183307613618937431 285772801774961420428406147)
    ·
      refine ⟨428659202662442130642609221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285772801774961420428406147 428659202662442130642609221)
      ·
        refine ⟨80373600499207899495489229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 428659202662442130642609221 80373600499207899495489229)
        ·
          refine ⟨30140100187202962310808461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80373600499207899495489229 30140100187202962310808461)
          ·
            refine ⟨11302537570201110866553173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30140100187202962310808461 11302537570201110866553173)
            ·
              refine ⟨33112903037698566991855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11302537570201110866553173 33112903037698566991855)
              ·
                rfl

theorem cell23_5223459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 10].length) (baseStart_5223459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5223459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5223459 prefixEnd_5223459 := by exact prefixLift 5223459
  have htrace : WordTrace (prefixWord ++ tailWord_5223459) baseStart_5223459 baseEnd_5223459 := by
    simpa [prefixWord, tailWord_5223459, baseEnd_5223459] using wordTrace_append hprefix tailTrace_5223459
  have hstable : (prefixWord ++ tailWord_5223459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5223459).length < 2 ^ (prefixWord ++ tailWord_5223459).sum := by decide
  have hdescent : baseEnd_5223459 < baseStart_5223459 := by decide
  rcases family_descends (prefixWord ++ tailWord_5223459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5223480 : List Nat := [2, 1, 2, 1, 5, 2, 3, 1, 2, 4]
def baseStart_5223480 : Nat := 118140960795 + 5223480 * 2 ^ 59
def prefixEnd_5223480 : Nat := 4983230072969 + 3 ^ 40 * 5223480 * 2
def baseEnd_5223480 : Nat := 894051976382442781392553

theorem tailTrace_5223480 : CollatzResearch.WordTrace tailWord_5223480 prefixEnd_5223480 894051976382442781392553 := by
  unfold tailWord_5223480
  simp only [CollatzResearch.WordTrace]
  refine ⟨95257983558115767102725947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127010644744154356136967929 95257983558115767102725947)
  ·
    refine ⟨142886975337173650654088921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95257983558115767102725947 142886975337173650654088921)
    ·
      refine ⟨107165231502880237990566691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142886975337173650654088921 107165231502880237990566691)
      ·
        refine ⟨160747847254320356985850037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107165231502880237990566691 160747847254320356985850037)
        ·
          refine ⟨15070110680092533467423441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 160747847254320356985850037 15070110680092533467423441)
          ·
            refine ⟨11302583010069400100567581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15070110680092533467423441 11302583010069400100567581)
            ·
              refine ⟨4238468628776025037712843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11302583010069400100567581 4238468628776025037712843)
              ·
                refine ⟨6357702943164037556569265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4238468628776025037712843 6357702943164037556569265)
                ·
                  refine ⟨4768277207373028167426949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6357702943164037556569265 4768277207373028167426949)
                  ·
                    refine ⟨894051976382442781392553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4768277207373028167426949 894051976382442781392553)
                    ·
                      rfl

theorem cell23_5223480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 3, 1, 2, 4].length) (baseStart_5223480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5223480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5223480 prefixEnd_5223480 := by exact prefixLift 5223480
  have htrace : WordTrace (prefixWord ++ tailWord_5223480) baseStart_5223480 baseEnd_5223480 := by
    simpa [prefixWord, tailWord_5223480, baseEnd_5223480] using wordTrace_append hprefix tailTrace_5223480
  have hstable : (prefixWord ++ tailWord_5223480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5223480).length < 2 ^ (prefixWord ++ tailWord_5223480).sum := by decide
  have hdescent : baseEnd_5223480 < baseStart_5223480 := by decide
  rcases family_descends (prefixWord ++ tailWord_5223480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5223510 : List Nat := [5, 2, 2, 1, 2, 2, 9]
def baseStart_5223510 : Nat := 118140960795 + 5223510 * 2 ^ 59
def prefixEnd_5223510 : Nat := 4983230072969 + 3 ^ 40 * 5223510 * 2
def baseEnd_5223510 : Nat := 33113226340332879343241

theorem tailTrace_5223510 : CollatzResearch.WordTrace tailWord_5223510 prefixEnd_5223510 33113226340332879343241 := by
  unfold tailWord_5223510
  simp only [CollatzResearch.WordTrace]
  refine ⟨11907316331632678083065249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 127011374204081899552695989 11907316331632678083065249)
  ·
    refine ⟨8930487248724508562298937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11907316331632678083065249 8930487248724508562298937)
    ·
      refine ⟨6697865436543381421724203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8930487248724508562298937 6697865436543381421724203)
      ·
        refine ⟨10046798154815072132586305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6697865436543381421724203 10046798154815072132586305)
        ·
          refine ⟨7535098616111304099439729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10046798154815072132586305 7535098616111304099439729)
          ·
            refine ⟨5651323962083478074579797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7535098616111304099439729 5651323962083478074579797)
            ·
              refine ⟨33113226340332879343241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5651323962083478074579797 33113226340332879343241)
              ·
                rfl

theorem cell23_5223510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 9].length) (baseStart_5223510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5223510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5223510 prefixEnd_5223510 := by exact prefixLift 5223510
  have htrace : WordTrace (prefixWord ++ tailWord_5223510) baseStart_5223510 baseEnd_5223510 := by
    simpa [prefixWord, tailWord_5223510, baseEnd_5223510] using wordTrace_append hprefix tailTrace_5223510
  have hstable : (prefixWord ++ tailWord_5223510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5223510).length < 2 ^ (prefixWord ++ tailWord_5223510).sum := by decide
  have hdescent : baseEnd_5223510 < baseStart_5223510 := by decide
  rcases family_descends (prefixWord ++ tailWord_5223510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5223516 : List Nat := [2, 2, 4, 1, 1, 1, 1, 2, 2, 2, 5]
def baseStart_5223516 : Nat := 118140960795 + 5223516 * 2 ^ 59
def prefixEnd_5223516 : Nat := 4983230072969 + 3 ^ 40 * 5223516 * 2
def baseEnd_5223516 : Nat := 2682174414450890203327493

theorem tailTrace_5223516 : CollatzResearch.WordTrace tailWord_5223516 prefixEnd_5223516 2682174414450890203327493 := by
  unfold tailWord_5223516
  simp only [CollatzResearch.WordTrace]
  refine ⟨95258640072050556176881201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127011520096067408235841601 95258640072050556176881201)
  ·
    refine ⟨71443980054037917132660901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95258640072050556176881201 71443980054037917132660901)
    ·
      refine ⟨13395746260132109462373919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71443980054037917132660901 13395746260132109462373919)
      ·
        refine ⟨20093619390198164193560879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13395746260132109462373919 20093619390198164193560879)
        ·
          refine ⟨30140429085297246290341319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20093619390198164193560879 30140429085297246290341319)
          ·
            refine ⟨45210643627945869435511979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30140429085297246290341319 45210643627945869435511979)
            ·
              refine ⟨67815965441918804153267969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45210643627945869435511979 67815965441918804153267969)
              ·
                refine ⟨50861974081439103114950977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67815965441918804153267969 50861974081439103114950977)
                ·
                  refine ⟨38146480561079327336213233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50861974081439103114950977 38146480561079327336213233)
                  ·
                    refine ⟨28609860420809495502159925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38146480561079327336213233 28609860420809495502159925)
                    ·
                      refine ⟨2682174414450890203327493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28609860420809495502159925 2682174414450890203327493)
                      ·
                        rfl

theorem cell23_5223516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_5223516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5223516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5223516 prefixEnd_5223516 := by exact prefixLift 5223516
  have htrace : WordTrace (prefixWord ++ tailWord_5223516) baseStart_5223516 baseEnd_5223516 := by
    simpa [prefixWord, tailWord_5223516, baseEnd_5223516] using wordTrace_append hprefix tailTrace_5223516
  have hstable : (prefixWord ++ tailWord_5223516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5223516).length < 2 ^ (prefixWord ++ tailWord_5223516).sum := by decide
  have hdescent : baseEnd_5223516 < baseStart_5223516 := by decide
  rcases family_descends (prefixWord ++ tailWord_5223516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5223539 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 6]
def baseStart_5223539 : Nat := 118140960795 + 5223539 * 2 ^ 59
def prefixEnd_5223539 : Nat := 4983230072969 + 3 ^ 40 * 5223539 * 2
def baseEnd_5223539 : Nat := 2682186224505943613339887

theorem tailTrace_5223539 : CollatzResearch.WordTrace tailWord_5223539 prefixEnd_5223539 2682186224505943613339887 := by
  unfold tailWord_5223539
  simp only [CollatzResearch.WordTrace]
  refine ⟨190518119023017787281849671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127012079348678524854566447 190518119023017787281849671)
  ·
    refine ⟨285777178534526680922774507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190518119023017787281849671 285777178534526680922774507)
    ·
      refine ⟨428665767801790021384161761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285777178534526680922774507 428665767801790021384161761)
      ·
        refine ⟨321499325851342516038121321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 428665767801790021384161761 321499325851342516038121321)
        ·
          refine ⟨241124494388506887028590991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 321499325851342516038121321 241124494388506887028590991)
          ·
            refine ⟨361686741582760330542886487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241124494388506887028590991 361686741582760330542886487)
            ·
              refine ⟨542530112374140495814329731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 361686741582760330542886487 542530112374140495814329731)
              ·
                refine ⟨813795168561210743721494597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 542530112374140495814329731 813795168561210743721494597)
                ·
                  refine ⟨152586594105227014447780237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 813795168561210743721494597 152586594105227014447780237)
                  ·
                    refine ⟨57219972789460130417917589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 152586594105227014447780237 57219972789460130417917589)
                    ·
                      refine ⟨2682186224505943613339887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57219972789460130417917589 2682186224505943613339887)
                      ·
                        rfl

theorem cell23_5223539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 3, 6].length) (baseStart_5223539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5223539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5223539 prefixEnd_5223539 := by exact prefixLift 5223539
  have htrace : WordTrace (prefixWord ++ tailWord_5223539) baseStart_5223539 baseEnd_5223539 := by
    simpa [prefixWord, tailWord_5223539, baseEnd_5223539] using wordTrace_append hprefix tailTrace_5223539
  have hstable : (prefixWord ++ tailWord_5223539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5223539).length < 2 ^ (prefixWord ++ tailWord_5223539).sum := by decide
  have hdescent : baseEnd_5223539 < baseStart_5223539 := by decide
  rcases family_descends (prefixWord ++ tailWord_5223539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5223543 : List Nat := [1, 1, 3, 1, 1, 4, 2, 3, 1, 4, 2]
def baseStart_5223543 : Nat := 118140960795 + 5223543 * 2 ^ 59
def prefixEnd_5223543 : Nat := 4983230072969 + 3 ^ 40 * 5223543 * 2
def baseEnd_5223543 : Nat := 2682188278428561597689869

theorem tailTrace_5223543 : CollatzResearch.WordTrace tailWord_5223543 prefixEnd_5223543 2682188278428561597689869 := by
  unfold tailWord_5223543
  simp only [CollatzResearch.WordTrace]
  refine ⟨190518264915003295964995283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127012176610002197309996855 190518264915003295964995283)
  ·
    refine ⟨285777397372504943947492925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190518264915003295964995283 285777397372504943947492925)
    ·
      refine ⟨107166524014689353980309847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 285777397372504943947492925 107166524014689353980309847)
      ·
        refine ⟨160749786022034030970464771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107166524014689353980309847 160749786022034030970464771)
        ·
          refine ⟨241124679033051046455697157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160749786022034030970464771 241124679033051046455697157)
          ·
            refine ⟨45210877318697071210443217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 241124679033051046455697157 45210877318697071210443217)
            ·
              refine ⟨33908157989022803407832413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45210877318697071210443217 33908157989022803407832413)
              ·
                refine ⟨12715559245883551277937155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33908157989022803407832413 12715559245883551277937155)
                ·
                  refine ⟨19073338868825326916905733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12715559245883551277937155 19073338868825326916905733)
                  ·
                    refine ⟨3576251037904748796919825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19073338868825326916905733 3576251037904748796919825)
                    ·
                      refine ⟨2682188278428561597689869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3576251037904748796919825 2682188278428561597689869)
                      ·
                        rfl

theorem cell23_5223543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 3, 1, 4, 2].length) (baseStart_5223543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5223543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5223543 prefixEnd_5223543 := by exact prefixLift 5223543
  have htrace : WordTrace (prefixWord ++ tailWord_5223543) baseStart_5223543 baseEnd_5223543 := by
    simpa [prefixWord, tailWord_5223543, baseEnd_5223543] using wordTrace_append hprefix tailTrace_5223543
  have hstable : (prefixWord ++ tailWord_5223543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5223543).length < 2 ^ (prefixWord ++ tailWord_5223543).sum := by decide
  have hdescent : baseEnd_5223543 < baseStart_5223543 := by decide
  rcases family_descends (prefixWord ++ tailWord_5223543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5223594 : List Nat := [3, 1, 5, 1, 1, 1, 2, 3, 2, 2, 2]
def baseStart_5223594 : Nat := 118140960795 + 5223594 * 2 ^ 59
def prefixEnd_5223594 : Nat := 4983230072969 + 3 ^ 40 * 5223594 * 2
def baseEnd_5223594 : Nat := 2682214465941940898152135

theorem tailTrace_5223594 : CollatzResearch.WordTrace tailWord_5223594 prefixEnd_5223594 2682214465941940898152135 := by
  unfold tailWord_5223594
  simp only [CollatzResearch.WordTrace]
  refine ⟨47630031259454632918775459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127013416691879021116734557 47630031259454632918775459)
  ·
    refine ⟨71445046889181949378163189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47630031259454632918775459 71445046889181949378163189)
    ·
      refine ⟨6697973145860807754202799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 71445046889181949378163189 6697973145860807754202799)
      ·
        refine ⟨10046959718791211631304199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6697973145860807754202799 10046959718791211631304199)
        ·
          refine ⟨15070439578186817446956299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10046959718791211631304199 15070439578186817446956299)
          ·
            refine ⟨22605659367280226170434449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15070439578186817446956299 22605659367280226170434449)
            ·
              refine ⟨16954244525460169627825837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22605659367280226170434449 16954244525460169627825837)
              ·
                refine ⟨6357841697047563610434689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16954244525460169627825837 6357841697047563610434689)
                ·
                  refine ⟨4768381272785672707826017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6357841697047563610434689 4768381272785672707826017)
                  ·
                    refine ⟨3576285954589254530869513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4768381272785672707826017 3576285954589254530869513)
                    ·
                      refine ⟨2682214465941940898152135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3576285954589254530869513 2682214465941940898152135)
                      ·
                        rfl

theorem cell23_5223594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_5223594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5223594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5223594 prefixEnd_5223594 := by exact prefixLift 5223594
  have htrace : WordTrace (prefixWord ++ tailWord_5223594) baseStart_5223594 baseEnd_5223594 := by
    simpa [prefixWord, tailWord_5223594, baseEnd_5223594] using wordTrace_append hprefix tailTrace_5223594
  have hstable : (prefixWord ++ tailWord_5223594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5223594).length < 2 ^ (prefixWord ++ tailWord_5223594).sum := by decide
  have hdescent : baseEnd_5223594 < baseStart_5223594 := by decide
  rcases family_descends (prefixWord ++ tailWord_5223594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5223613 : List Nat := [1, 4, 1, 2, 1, 1, 5, 1, 2, 5]
def baseStart_5223613 : Nat := 118140960795 + 5223613 * 2 ^ 59
def prefixEnd_5223613 : Nat := 4983230072969 + 3 ^ 40 * 5223613 * 2
def baseEnd_5223613 : Nat := 894074740691458774604849

theorem tailTrace_5223613 : CollatzResearch.WordTrace tailWord_5223613 prefixEnd_5223613 894074740691458774604849 := by
  unfold tailWord_5223613
  simp only [CollatzResearch.WordTrace]
  refine ⟨190520818024749697920043493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127013878683166465280028995 190520818024749697920043493)
  ·
    refine ⟨35722653379640568360008155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 190520818024749697920043493 35722653379640568360008155)
    ·
      refine ⟨53583980069460852540012233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35722653379640568360008155 53583980069460852540012233)
      ·
        refine ⟨40187985052095639405009175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53583980069460852540012233 40187985052095639405009175)
        ·
          refine ⟨60281977578143459107513763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40187985052095639405009175 60281977578143459107513763)
          ·
            refine ⟨90422966367215188661270645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60281977578143459107513763 90422966367215188661270645)
            ·
              refine ⟨8477153096926423936994123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 90422966367215188661270645 8477153096926423936994123)
              ·
                refine ⟨12715729645389635905491185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8477153096926423936994123 12715729645389635905491185)
                ·
                  refine ⟨9536797234042226929118389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12715729645389635905491185 9536797234042226929118389)
                  ·
                    refine ⟨894074740691458774604849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9536797234042226929118389 894074740691458774604849)
                    ·
                      rfl

theorem cell23_5223613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 1, 2, 5].length) (baseStart_5223613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5223613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5223613 prefixEnd_5223613 := by exact prefixLift 5223613
  have htrace : WordTrace (prefixWord ++ tailWord_5223613) baseStart_5223613 baseEnd_5223613 := by
    simpa [prefixWord, tailWord_5223613, baseEnd_5223613] using wordTrace_append hprefix tailTrace_5223613
  have hstable : (prefixWord ++ tailWord_5223613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5223613).length < 2 ^ (prefixWord ++ tailWord_5223613).sum := by decide
  have hdescent : baseEnd_5223613 < baseStart_5223613 := by decide
  rcases family_descends (prefixWord ++ tailWord_5223613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5223617 : List Nat := [1, 2, 6, 1, 1, 2, 2, 3, 5]
def baseStart_5223617 : Nat := 118140960795 + 5223617 * 2 ^ 59
def prefixEnd_5223617 : Nat := 4983230072969 + 3 ^ 40 * 5223617 * 2
def baseEnd_5223617 : Nat := 298025141777443812018281

theorem tailTrace_5223617 : CollatzResearch.WordTrace tailWord_5223617 prefixEnd_5223617 298025141777443812018281 := by
  unfold tailWord_5223617
  simp only [CollatzResearch.WordTrace]
  refine ⟨190520963916735206603189105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127013975944490137735459403 190520963916735206603189105)
  ·
    refine ⟨142890722937551404952391829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190520963916735206603189105 142890722937551404952391829)
    ·
      refine ⟨6698002637697722107143367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 142890722937551404952391829 6698002637697722107143367)
      ·
        refine ⟨10047003956546583160715051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6698002637697722107143367 10047003956546583160715051)
        ·
          refine ⟨15070505934819874741072577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10047003956546583160715051 15070505934819874741072577)
          ·
            refine ⟨11302879451114906055804433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15070505934819874741072577 11302879451114906055804433)
            ·
              refine ⟨8477159588336179541853325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11302879451114906055804433 8477159588336179541853325)
              ·
                refine ⟨3178934845626067328194997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8477159588336179541853325 3178934845626067328194997)
                ·
                  refine ⟨298025141777443812018281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3178934845626067328194997 298025141777443812018281)
                  ·
                    rfl

theorem cell23_5223617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 3, 5].length) (baseStart_5223617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5223617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5223617 prefixEnd_5223617 := by exact prefixLift 5223617
  have htrace : WordTrace (prefixWord ++ tailWord_5223617) baseStart_5223617 baseEnd_5223617 := by
    simpa [prefixWord, tailWord_5223617, baseEnd_5223617] using wordTrace_append hprefix tailTrace_5223617
  have hstable : (prefixWord ++ tailWord_5223617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5223617).length < 2 ^ (prefixWord ++ tailWord_5223617).sum := by decide
  have hdescent : baseEnd_5223617 < baseStart_5223617 := by decide
  rcases family_descends (prefixWord ++ tailWord_5223617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5223668 : List Nat := [2, 6, 1, 2, 2, 1, 1, 3, 5]
def baseStart_5223668 : Nat := 118140960795 + 5223668 * 2 ^ 59
def prefixEnd_5223668 : Nat := 4983230072969 + 3 ^ 40 * 5223668 * 2
def baseEnd_5223668 : Nat := 298028051501152623180755

theorem tailTrace_5223668 : CollatzResearch.WordTrace tailWord_5223668 prefixEnd_5223668 298028051501152623180755 := by
  unfold tailWord_5223668
  simp only [CollatzResearch.WordTrace]
  refine ⟨95261412019775221156647829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127015216026366961542197105 95261412019775221156647829)
  ·
    refine ⟨4465378688426963491717867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 95261412019775221156647829 4465378688426963491717867)
    ·
      refine ⟨6698068032640445237576801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4465378688426963491717867 6698068032640445237576801)
      ·
        refine ⟨5023551024480333928182601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6698068032640445237576801 5023551024480333928182601)
        ·
          refine ⟨3767663268360250446136951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5023551024480333928182601 3767663268360250446136951)
          ·
            refine ⟨5651494902540375669205427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3767663268360250446136951 5651494902540375669205427)
            ·
              refine ⟨8477242353810563503808141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5651494902540375669205427 8477242353810563503808141)
              ·
                refine ⟨3178965882678961313928053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8477242353810563503808141 3178965882678961313928053)
                ·
                  refine ⟨298028051501152623180755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3178965882678961313928053 298028051501152623180755)
                  ·
                    rfl

theorem cell23_5223668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_5223668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5223668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5223668 prefixEnd_5223668 := by exact prefixLift 5223668
  have htrace : WordTrace (prefixWord ++ tailWord_5223668) baseStart_5223668 baseEnd_5223668 := by
    simpa [prefixWord, tailWord_5223668, baseEnd_5223668] using wordTrace_append hprefix tailTrace_5223668
  have hstable : (prefixWord ++ tailWord_5223668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5223668).length < 2 ^ (prefixWord ++ tailWord_5223668).sum := by decide
  have hdescent : baseEnd_5223668 < baseStart_5223668 := by decide
  rcases family_descends (prefixWord ++ tailWord_5223668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5223670 : List Nat := [5, 1, 1, 1, 1, 1, 1, 5, 2, 2, 3]
def baseStart_5223670 : Nat := 118140960795 + 5223670 * 2 ^ 59
def prefixEnd_5223670 : Nat := 4983230072969 + 3 ^ 40 * 5223670 * 2
def baseEnd_5223670 : Nat := 2682253490471682600801785

theorem tailTrace_5223670 : CollatzResearch.WordTrace tailWord_5223670 prefixEnd_5223670 2682253490471682600801785 := by
  unfold tailWord_5223670
  simp only [CollatzResearch.WordTrace]
  refine ⟨11907681061596449790929279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 127015264657028797769912309 11907681061596449790929279)
  ·
    refine ⟨17861521592394674686393919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11907681061596449790929279 17861521592394674686393919)
    ·
      refine ⟨26792282388592012029590879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17861521592394674686393919 26792282388592012029590879)
      ·
        refine ⟨40188423582888018044386319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26792282388592012029590879 40188423582888018044386319)
        ·
          refine ⟨60282635374332027066579479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40188423582888018044386319 60282635374332027066579479)
          ·
            refine ⟨90423953061498040599869219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60282635374332027066579479 90423953061498040599869219)
            ·
              refine ⟨135635929592247060899803829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90423953061498040599869219 135635929592247060899803829)
              ·
                refine ⟨12715868399273161959356609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 135635929592247060899803829 12715868399273161959356609)
                ·
                  refine ⟨9536901299454871469517457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12715868399273161959356609 9536901299454871469517457)
                  ·
                    refine ⟨7152675974591153602138093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9536901299454871469517457 7152675974591153602138093)
                    ·
                      refine ⟨2682253490471682600801785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7152675974591153602138093 2682253490471682600801785)
                      ·
                        rfl

theorem cell23_5223670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 5, 2, 2, 3].length) (baseStart_5223670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5223670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5223670 prefixEnd_5223670 := by exact prefixLift 5223670
  have htrace : WordTrace (prefixWord ++ tailWord_5223670) baseStart_5223670 baseEnd_5223670 := by
    simpa [prefixWord, tailWord_5223670, baseEnd_5223670] using wordTrace_append hprefix tailTrace_5223670
  have hstable : (prefixWord ++ tailWord_5223670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5223670).length < 2 ^ (prefixWord ++ tailWord_5223670).sum := by decide
  have hdescent : baseEnd_5223670 < baseStart_5223670 := by decide
  rcases family_descends (prefixWord ++ tailWord_5223670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5223694 : List Nat := [4, 1, 1, 2, 1, 4, 3, 2, 1, 4]
def baseStart_5223694 : Nat := 118140960795 + 5223694 * 2 ^ 59
def prefixEnd_5223694 : Nat := 4983230072969 + 3 ^ 40 * 5223694 * 2
def baseEnd_5223694 : Nat := 894088604669130168967225

theorem tailTrace_5223694 : CollatzResearch.WordTrace tailWord_5223694 prefixEnd_5223694 894088604669130168967225 := by
  unfold tailWord_5223694
  simp only [CollatzResearch.WordTrace]
  refine ⟨23815471542182031094217767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127015848224970832502494757 23815471542182031094217767)
  ·
    refine ⟨35723207313273046641326651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23815471542182031094217767 35723207313273046641326651)
    ·
      refine ⟨53584810969909569961989977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35723207313273046641326651 53584810969909569961989977)
      ·
        refine ⟨40188608227432177471492483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53584810969909569961989977 40188608227432177471492483)
        ·
          refine ⟨60282912341148266207238725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40188608227432177471492483 60282912341148266207238725)
          ·
            refine ⟨11303046063965299913857261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60282912341148266207238725 11303046063965299913857261)
            ·
              refine ⟨4238642273986987467696473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11303046063965299913857261 4238642273986987467696473)
              ·
                refine ⟨3178981705490240600772355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4238642273986987467696473 3178981705490240600772355)
                ·
                  refine ⟨4768472558235360901158533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3178981705490240600772355 4768472558235360901158533)
                  ·
                    refine ⟨894088604669130168967225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4768472558235360901158533 894088604669130168967225)
                    ·
                      rfl

theorem cell23_5223694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 3, 2, 1, 4].length) (baseStart_5223694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5223694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5223694 prefixEnd_5223694 := by exact prefixLift 5223694
  have htrace : WordTrace (prefixWord ++ tailWord_5223694) baseStart_5223694 baseEnd_5223694 := by
    simpa [prefixWord, tailWord_5223694, baseEnd_5223694] using wordTrace_append hprefix tailTrace_5223694
  have hstable : (prefixWord ++ tailWord_5223694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5223694).length < 2 ^ (prefixWord ++ tailWord_5223694).sum := by decide
  have hdescent : baseEnd_5223694 < baseStart_5223694 := by decide
  rcases family_descends (prefixWord ++ tailWord_5223694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5223703 : List Nat := [1, 1, 3, 4, 1, 1, 2, 2, 3, 5]
def baseStart_5223703 : Nat := 118140960795 + 5223703 * 2 ^ 59
def prefixEnd_5223703 : Nat := 4983230072969 + 3 ^ 40 * 5223703 * 2
def baseEnd_5223703 : Nat := 894090145111093657229711

theorem tailTrace_5223703 : CollatzResearch.WordTrace tailWord_5223703 prefixEnd_5223703 894090145111093657229711 := by
  unfold tailWord_5223703
  simp only [CollatzResearch.WordTrace]
  refine ⟨190524100594423643290819763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127016067062949095527213175 190524100594423643290819763)
  ·
    refine ⟨285786150891635464936229645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190524100594423643290819763 285786150891635464936229645)
    ·
      refine ⟨107169806584363299351086117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 285786150891635464936229645 107169806584363299351086117)
      ·
        refine ⟨20094338734568118628328647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107169806584363299351086117 20094338734568118628328647)
        ·
          refine ⟨30141508101852177942492971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20094338734568118628328647 30141508101852177942492971)
          ·
            refine ⟨45212262152778266913739457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30141508101852177942492971 45212262152778266913739457)
            ·
              refine ⟨33909196614583700185304593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45212262152778266913739457 33909196614583700185304593)
              ·
                refine ⟨25431897460937775138978445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33909196614583700185304593 25431897460937775138978445)
                ·
                  refine ⟨9536961547851665677116917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25431897460937775138978445 9536961547851665677116917)
                  ·
                    refine ⟨894090145111093657229711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9536961547851665677116917 894090145111093657229711)
                    ·
                      rfl

theorem cell23_5223703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 3, 5].length) (baseStart_5223703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5223703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5223703 prefixEnd_5223703 := by exact prefixLift 5223703
  have htrace : WordTrace (prefixWord ++ tailWord_5223703) baseStart_5223703 baseEnd_5223703 := by
    simpa [prefixWord, tailWord_5223703, baseEnd_5223703] using wordTrace_append hprefix tailTrace_5223703
  have hstable : (prefixWord ++ tailWord_5223703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5223703).length < 2 ^ (prefixWord ++ tailWord_5223703).sum := by decide
  have hdescent : baseEnd_5223703 < baseStart_5223703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5223703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5223720 : List Nat := [2, 1, 5, 1, 2, 2, 1, 1, 3, 5]
def baseStart_5223720 : Nat := 118140960795 + 5223720 * 2 ^ 59
def prefixEnd_5223720 : Nat := 4983230072969 + 3 ^ 40 * 5223720 * 2
def baseEnd_5223720 : Nat := 894093054834802468392185

theorem tailTrace_5223720 : CollatzResearch.WordTrace tailWord_5223720 prefixEnd_5223720 894093054834802468392185 := by
  unfold tailWord_5223720
  simp only [CollatzResearch.WordTrace]
  refine ⟨95262360317681027597094307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127016480423574703462792409 95262360317681027597094307)
  ·
    refine ⟨142893540476521541395641461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95262360317681027597094307 142893540476521541395641461)
    ·
      refine ⟨13396269419673894505841387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 142893540476521541395641461 13396269419673894505841387)
      ·
        refine ⟨20094404129510841758762081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13396269419673894505841387 20094404129510841758762081)
        ·
          refine ⟨15070803097133131319071561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20094404129510841758762081 15070803097133131319071561)
          ·
            refine ⟨11303102322849848489303671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15070803097133131319071561 11303102322849848489303671)
            ·
              refine ⟨16954653484274772733955507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11303102322849848489303671 16954653484274772733955507)
              ·
                refine ⟨25431980226412159100933261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16954653484274772733955507 25431980226412159100933261)
                ·
                  refine ⟨9536992584904559662849973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25431980226412159100933261 9536992584904559662849973)
                  ·
                    refine ⟨894093054834802468392185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9536992584904559662849973 894093054834802468392185)
                    ·
                      rfl

theorem cell23_5223720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_5223720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5223720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5223720 prefixEnd_5223720 := by exact prefixLift 5223720
  have htrace : WordTrace (prefixWord ++ tailWord_5223720) baseStart_5223720 baseEnd_5223720 := by
    simpa [prefixWord, tailWord_5223720, baseEnd_5223720] using wordTrace_append hprefix tailTrace_5223720
  have hstable : (prefixWord ++ tailWord_5223720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5223720).length < 2 ^ (prefixWord ++ tailWord_5223720).sum := by decide
  have hdescent : baseEnd_5223720 < baseStart_5223720 := by decide
  rcases family_descends (prefixWord ++ tailWord_5223720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5223733 : List Nat := [1, 3, 3, 1, 2, 2, 1, 1, 3, 6]
def baseStart_5223733 : Nat := 118140960795 + 5223733 * 2 ^ 59
def prefixEnd_5223733 : Nat := 4983230072969 + 3 ^ 40 * 5223733 * 2
def baseEnd_5223733 : Nat := 894095279917638618104665

theorem tailTrace_5223733 : CollatzResearch.WordTrace tailWord_5223733 prefixEnd_5223733 894095279917638618104665 := by
  unfold tailWord_5223733
  simp only [CollatzResearch.WordTrace]
  refine ⟨190525194784314958414411853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127016796522876638942941235 190525194784314958414411853)
  ·
    refine ⟨71446948044118109405404445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190525194784314958414411853 71446948044118109405404445)
    ·
      refine ⟨26792605516544291027026667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71446948044118109405404445 26792605516544291027026667)
      ·
        refine ⟨40188908274816436540540001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26792605516544291027026667 40188908274816436540540001)
        ·
          refine ⟨30141681206112327405405001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40188908274816436540540001 30141681206112327405405001)
          ·
            refine ⟨22606260904584245554053751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30141681206112327405405001 22606260904584245554053751)
            ·
              refine ⟨33909391356876368331080627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22606260904584245554053751 33909391356876368331080627)
              ·
                refine ⟨50864087035314552496620941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33909391356876368331080627 50864087035314552496620941)
                ·
                  refine ⟨19074032638242957186232853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50864087035314552496620941 19074032638242957186232853)
                  ·
                    refine ⟨894095279917638618104665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19074032638242957186232853 894095279917638618104665)
                    ·
                      rfl

theorem cell23_5223733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_5223733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5223733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5223733 prefixEnd_5223733 := by exact prefixLift 5223733
  have htrace : WordTrace (prefixWord ++ tailWord_5223733) baseStart_5223733 baseEnd_5223733 := by
    simpa [prefixWord, tailWord_5223733, baseEnd_5223733] using wordTrace_append hprefix tailTrace_5223733
  have hstable : (prefixWord ++ tailWord_5223733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5223733).length < 2 ^ (prefixWord ++ tailWord_5223733).sum := by decide
  have hdescent : baseEnd_5223733 < baseStart_5223733 := by decide
  rcases family_descends (prefixWord ++ tailWord_5223733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5223746 : List Nat := [3, 20]
def baseStart_5223746 : Nat := 118140960795 + 5223746 * 2 ^ 59
def prefixEnd_5223746 : Nat := 4983230072969 + 3 ^ 40 * 5223746 * 2
def baseEnd_5223746 : Nat := 136274577808333297945

theorem tailTrace_5223746 : CollatzResearch.WordTrace tailWord_5223746 prefixEnd_5223746 136274577808333297945 := by
  unfold tailWord_5223746
  simp only [CollatzResearch.WordTrace]
  refine ⟨47631417233316965408658773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127017112622178574423090061 47631417233316965408658773)
  ·
    refine ⟨136274577808333297945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 20 47631417233316965408658773 136274577808333297945)
    ·
      rfl

theorem cell23_5223746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 20].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 20].length) (baseStart_5223746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5223746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5223746 prefixEnd_5223746 := by exact prefixLift 5223746
  have htrace : WordTrace (prefixWord ++ tailWord_5223746) baseStart_5223746 baseEnd_5223746 := by
    simpa [prefixWord, tailWord_5223746, baseEnd_5223746] using wordTrace_append hprefix tailTrace_5223746
  have hstable : (prefixWord ++ tailWord_5223746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5223746).length < 2 ^ (prefixWord ++ tailWord_5223746).sum := by decide
  have hdescent : baseEnd_5223746 < baseStart_5223746 := by decide
  rcases family_descends (prefixWord ++ tailWord_5223746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5223751 : List Nat := [1, 1, 4, 1, 2, 5, 2, 2, 1, 1, 3]
def baseStart_5223751 : Nat := 118140960795 + 5223751 * 2 ^ 59
def prefixEnd_5223751 : Nat := 4983230072969 + 3 ^ 40 * 5223751 * 2
def baseEnd_5223751 : Nat := 2682295082404696783888913

theorem tailTrace_5223751 : CollatzResearch.WordTrace tailWord_5223751 prefixEnd_5223751 2682295082404696783888913 := by
  unfold tailWord_5223751
  simp only [CollatzResearch.WordTrace]
  refine ⟨190525851298249747488567107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127017234198833164992378071 190525851298249747488567107)
  ·
    refine ⟨285788776947374621232850661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190525851298249747488567107 285788776947374621232850661)
    ·
      refine ⟨53585395677632741481159499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 285788776947374621232850661 53585395677632741481159499)
      ·
        refine ⟨80378093516449112221739249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53585395677632741481159499 80378093516449112221739249)
        ·
          refine ⟨60283570137336834166304437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80378093516449112221739249 60283570137336834166304437)
          ·
            refine ⟨5651584700375328203091041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60283570137336834166304437 5651584700375328203091041)
            ·
              refine ⟨4238688525281496152318281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5651584700375328203091041 4238688525281496152318281)
              ·
                refine ⟨3179016393961122114238711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4238688525281496152318281 3179016393961122114238711)
                ·
                  refine ⟨4768524590941683171358067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3179016393961122114238711 4768524590941683171358067)
                  ·
                    refine ⟨7152786886412524757037101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4768524590941683171358067 7152786886412524757037101)
                    ·
                      refine ⟨2682295082404696783888913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7152786886412524757037101 2682295082404696783888913)
                      ·
                        rfl

theorem cell23_5223751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 2, 2, 1, 1, 3].length) (baseStart_5223751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5223751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5223751 prefixEnd_5223751 := by exact prefixLift 5223751
  have htrace : WordTrace (prefixWord ++ tailWord_5223751) baseStart_5223751 baseEnd_5223751 := by
    simpa [prefixWord, tailWord_5223751, baseEnd_5223751] using wordTrace_append hprefix tailTrace_5223751
  have hstable : (prefixWord ++ tailWord_5223751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5223751).length < 2 ^ (prefixWord ++ tailWord_5223751).sum := by decide
  have hdescent : baseEnd_5223751 < baseStart_5223751 := by decide
  rcases family_descends (prefixWord ++ tailWord_5223751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5223780 : List Nat := [2, 3, 1, 1, 3, 3, 3, 7]
def baseStart_5223780 : Nat := 118140960795 + 5223780 * 2 ^ 59
def prefixEnd_5223780 : Nat := 4983230072969 + 3 ^ 40 * 5223780 * 2
def baseEnd_5223780 : Nat := 99344813827543598904677

theorem tailTrace_5223780 : CollatzResearch.WordTrace tailWord_5223780 prefixEnd_5223780 99344813827543598904677 := by
  unfold tailWord_5223780
  simp only [CollatzResearch.WordTrace]
  refine ⟨95263454507572342720686397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127017939343429790294248529 95263454507572342720686397)
  ·
    refine ⟨35723795440339628520257399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95263454507572342720686397 35723795440339628520257399)
    ·
      refine ⟨53585693160509442780386099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35723795440339628520257399 53585693160509442780386099)
      ·
        refine ⟨80378539740764164170579149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53585693160509442780386099 80378539740764164170579149)
        ·
          refine ⟨30141952402786561563967181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80378539740764164170579149 30141952402786561563967181)
          ·
            refine ⟨11303232151044960586487693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30141952402786561563967181 11303232151044960586487693)
            ·
              refine ⟨4238712056641860219932885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11303232151044960586487693 4238712056641860219932885)
              ·
                refine ⟨99344813827543598904677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4238712056641860219932885 99344813827543598904677)
                ·
                  rfl

theorem cell23_5223780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 3, 7].length) (baseStart_5223780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5223780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5223780 prefixEnd_5223780 := by exact prefixLift 5223780
  have htrace : WordTrace (prefixWord ++ tailWord_5223780) baseStart_5223780 baseEnd_5223780 := by
    simpa [prefixWord, tailWord_5223780, baseEnd_5223780] using wordTrace_append hprefix tailTrace_5223780
  have hstable : (prefixWord ++ tailWord_5223780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5223780).length < 2 ^ (prefixWord ++ tailWord_5223780).sum := by decide
  have hdescent : baseEnd_5223780 < baseStart_5223780 := by decide
  rcases family_descends (prefixWord ++ tailWord_5223780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5223813 : List Nat := [1, 3, 1, 1, 3, 1, 2, 1, 1, 5, 4]
def baseStart_5223813 : Nat := 118140960795 + 5223813 * 2 ^ 59
def prefixEnd_5223813 : Nat := 4983230072969 + 3 ^ 40 * 5223813 * 2
def baseEnd_5223813 : Nat := 2682326918205275541313627

theorem tailTrace_5223813 : CollatzResearch.WordTrace tailWord_5223813 prefixEnd_5223813 2682326918205275541313627 := by
  unfold tailWord_5223813
  simp only [CollatzResearch.WordTrace]
  refine ⟨190528112624025132077324093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127018741749350088051549395 190528112624025132077324093)
  ·
    refine ⟨71448042234009424528996535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190528112624025132077324093 71448042234009424528996535)
    ·
      refine ⟨107172063351014136793494803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71448042234009424528996535 107172063351014136793494803)
      ·
        refine ⟨160758095026521205190242205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107172063351014136793494803 160758095026521205190242205)
        ·
          refine ⟨60284285634945451946340827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 160758095026521205190242205 60284285634945451946340827)
          ·
            refine ⟨90426428452418177919511241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60284285634945451946340827 90426428452418177919511241)
            ·
              refine ⟨67819821339313633439633431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90426428452418177919511241 67819821339313633439633431)
              ·
                refine ⟨101729732008970450159450147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67819821339313633439633431 101729732008970450159450147)
                ·
                  refine ⟨152594598013455675239175221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101729732008970450159450147 152594598013455675239175221)
                  ·
                    refine ⟨14305743563761469553672677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 152594598013455675239175221 14305743563761469553672677)
                    ·
                      refine ⟨2682326918205275541313627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14305743563761469553672677 2682326918205275541313627)
                      ·
                        rfl

theorem cell23_5223813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 5, 4].length) (baseStart_5223813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5223813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5223813 prefixEnd_5223813 := by exact prefixLift 5223813
  have htrace : WordTrace (prefixWord ++ tailWord_5223813) baseStart_5223813 baseEnd_5223813 := by
    simpa [prefixWord, tailWord_5223813, baseEnd_5223813] using wordTrace_append hprefix tailTrace_5223813
  have hstable : (prefixWord ++ tailWord_5223813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5223813).length < 2 ^ (prefixWord ++ tailWord_5223813).sum := by decide
  have hdescent : baseEnd_5223813 < baseStart_5223813 := by decide
  rcases family_descends (prefixWord ++ tailWord_5223813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5223834 : List Nat := [3, 1, 1, 4, 1, 1, 4, 2, 1, 3, 2]
def baseStart_5223834 : Nat := 118140960795 + 5223834 * 2 ^ 59
def prefixEnd_5223834 : Nat := 4983230072969 + 3 ^ 40 * 5223834 * 2
def baseEnd_5223834 : Nat := 2682337701299019959151031

theorem tailTrace_5223834 : CollatzResearch.WordTrace tailWord_5223834 prefixEnd_5223834 2682337701299019959151031 := by
  unfold tailWord_5223834
  simp only [CollatzResearch.WordTrace]
  refine ⟨47632219639237263165959639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127019252371299368442559037 47632219639237263165959639)
  ·
    refine ⟨71448329458855894748939459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47632219639237263165959639 71448329458855894748939459)
    ·
      refine ⟨107172494188283842123409189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71448329458855894748939459 107172494188283842123409189)
      ·
        refine ⟨20094842660303220398139223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107172494188283842123409189 20094842660303220398139223)
        ·
          refine ⟨30142263990454830597208835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20094842660303220398139223 30142263990454830597208835)
          ·
            refine ⟨45213395985682245895813253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30142263990454830597208835 45213395985682245895813253)
            ·
              refine ⟨8477511747315421105464985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45213395985682245895813253 8477511747315421105464985)
              ·
                refine ⟨6358133810486565829098739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8477511747315421105464985 6358133810486565829098739)
                ·
                  refine ⟨9537200715729848743648109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6358133810486565829098739 9537200715729848743648109)
                  ·
                    refine ⟨3576450268398693278868041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9537200715729848743648109 3576450268398693278868041)
                    ·
                      refine ⟨2682337701299019959151031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3576450268398693278868041 2682337701299019959151031)
                      ·
                        rfl

theorem cell23_5223834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 2, 1, 3, 2].length) (baseStart_5223834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5223834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5223834 prefixEnd_5223834 := by exact prefixLift 5223834
  have htrace : WordTrace (prefixWord ++ tailWord_5223834) baseStart_5223834 baseEnd_5223834 := by
    simpa [prefixWord, tailWord_5223834, baseEnd_5223834] using wordTrace_append hprefix tailTrace_5223834
  have hstable : (prefixWord ++ tailWord_5223834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5223834).length < 2 ^ (prefixWord ++ tailWord_5223834).sum := by decide
  have hdescent : baseEnd_5223834 < baseStart_5223834 := by decide
  rcases family_descends (prefixWord ++ tailWord_5223834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5223847 : List Nat := [1, 1, 6, 1, 1, 1, 2, 1, 3, 4, 2]
def baseStart_5223847 : Nat := 118140960795 + 5223847 * 2 ^ 59
def prefixEnd_5223847 : Nat := 4983230072969 + 3 ^ 40 * 5223847 * 2
def baseEnd_5223847 : Nat := 2682344376547528408288471

theorem tailTrace_5223847 : CollatzResearch.WordTrace tailWord_5223847 prefixEnd_5223847 2682344376547528408288471 := by
  unfold tailWord_5223847
  simp only [CollatzResearch.WordTrace]
  refine ⟨190529352705901955884061795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127019568470601303922707863 190529352705901955884061795)
  ·
    refine ⟨285794029058852933826092693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190529352705901955884061795 285794029058852933826092693)
    ·
      refine ⟨13396595112133731273098095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 285794029058852933826092693 13396595112133731273098095)
      ·
        refine ⟨20094892668200596909647143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13396595112133731273098095 20094892668200596909647143)
        ·
          refine ⟨30142339002300895364470715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20094892668200596909647143 30142339002300895364470715)
          ·
            refine ⟨45213508503451343046706073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30142339002300895364470715 45213508503451343046706073)
            ·
              refine ⟨33910131377588507285029555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45213508503451343046706073 33910131377588507285029555)
              ·
                refine ⟨50865197066382760927544333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33910131377588507285029555 50865197066382760927544333)
                ·
                  refine ⟨19074448899893535347829125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50865197066382760927544333 19074448899893535347829125)
                  ·
                    refine ⟨3576459168730037877717961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19074448899893535347829125 3576459168730037877717961)
                    ·
                      refine ⟨2682344376547528408288471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3576459168730037877717961 2682344376547528408288471)
                      ·
                        rfl

theorem cell23_5223847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 3, 4, 2].length) (baseStart_5223847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5223847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5223847 prefixEnd_5223847 := by exact prefixLift 5223847
  have htrace : WordTrace (prefixWord ++ tailWord_5223847) baseStart_5223847 baseEnd_5223847 := by
    simpa [prefixWord, tailWord_5223847, baseEnd_5223847] using wordTrace_append hprefix tailTrace_5223847
  have hstable : (prefixWord ++ tailWord_5223847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5223847).length < 2 ^ (prefixWord ++ tailWord_5223847).sum := by decide
  have hdescent : baseEnd_5223847 < baseStart_5223847 := by decide
  rcases family_descends (prefixWord ++ tailWord_5223847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5223863 : List Nat := [1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 7]
def baseStart_5223863 : Nat := 118140960795 + 5223863 * 2 ^ 59
def prefixEnd_5223863 : Nat := 4983230072969 + 3 ^ 40 * 5223863 * 2
def baseEnd_5223863 : Nat := 2682352592238000345688397

theorem tailTrace_5223863 : CollatzResearch.WordTrace tailWord_5223863 prefixEnd_5223863 2682352592238000345688397 := by
  unfold tailWord_5223863
  simp only [CollatzResearch.WordTrace]
  refine ⟨190529936273843990616644243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127019957515895993744429495 190529936273843990616644243)
  ·
    refine ⟨285794904410765985924966365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190529936273843990616644243 285794904410765985924966365)
    ·
      refine ⟨107173089154037244721862387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 285794904410765985924966365 107173089154037244721862387)
      ·
        refine ⟨160759633731055867082793581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107173089154037244721862387 160759633731055867082793581)
        ·
          refine ⟨60284862649145950156047593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 160759633731055867082793581 60284862649145950156047593)
          ·
            refine ⟨45213646986859462617035695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60284862649145950156047593 45213646986859462617035695)
            ·
              refine ⟨67820470480289193925553543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45213646986859462617035695 67820470480289193925553543)
              ·
                refine ⟨101730705720433790888330315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67820470480289193925553543 101730705720433790888330315)
                ·
                  refine ⟨152596058580650686332495473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101730705720433790888330315 152596058580650686332495473)
                  ·
                    refine ⟨114447043935488014749371605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 152596058580650686332495473 114447043935488014749371605)
                    ·
                      refine ⟨2682352592238000345688397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 114447043935488014749371605 2682352592238000345688397)
                      ·
                        rfl

theorem cell23_5223863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 7].length) (baseStart_5223863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5223863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5223863 prefixEnd_5223863 := by exact prefixLift 5223863
  have htrace : WordTrace (prefixWord ++ tailWord_5223863) baseStart_5223863 baseEnd_5223863 := by
    simpa [prefixWord, tailWord_5223863, baseEnd_5223863] using wordTrace_append hprefix tailTrace_5223863
  have hstable : (prefixWord ++ tailWord_5223863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5223863).length < 2 ^ (prefixWord ++ tailWord_5223863).sum := by decide
  have hdescent : baseEnd_5223863 < baseStart_5223863 := by decide
  rcases family_descends (prefixWord ++ tailWord_5223863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5223880 : List Nat := [2, 1, 3, 1, 3, 1, 2, 1, 1, 5, 3]
def baseStart_5223880 : Nat := 118140960795 + 5223880 * 2 ^ 59
def prefixEnd_5223880 : Nat := 4983230072969 + 3 ^ 40 * 5223880 * 2
def baseEnd_5223880 : Nat := 2682361321409126779175819

theorem tailTrace_5223880 : CollatzResearch.WordTrace tailWord_5223880 prefixEnd_5223880 2682361321409126779175819 := by
  unfold tailWord_5223880
  simp only [CollatzResearch.WordTrace]
  refine ⟨95265278157391201260006547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127020370876521601680008729 95265278157391201260006547)
  ·
    refine ⟨142897917236086801890009821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95265278157391201260006547 142897917236086801890009821)
    ·
      refine ⟨53586718963532550708753683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142897917236086801890009821 53586718963532550708753683)
      ·
        refine ⟨80380078445298826063130525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53586718963532550708753683 80380078445298826063130525)
        ·
          refine ⟨30142529416987059773673947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80380078445298826063130525 30142529416987059773673947)
          ·
            refine ⟨45213794125480589660510921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30142529416987059773673947 45213794125480589660510921)
            ·
              refine ⟨33910345594110442245383191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45213794125480589660510921 33910345594110442245383191)
              ·
                refine ⟨50865518391165663368074787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33910345594110442245383191 50865518391165663368074787)
                ·
                  refine ⟨76298277586748495052112181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50865518391165663368074787 76298277586748495052112181)
                  ·
                    refine ⟨7152963523757671411135517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 76298277586748495052112181 7152963523757671411135517)
                    ·
                      refine ⟨2682361321409126779175819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7152963523757671411135517 2682361321409126779175819)
                      ·
                        rfl

theorem cell23_5223880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 1, 5, 3].length) (baseStart_5223880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5223880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5223880 prefixEnd_5223880 := by exact prefixLift 5223880
  have htrace : WordTrace (prefixWord ++ tailWord_5223880) baseStart_5223880 baseEnd_5223880 := by
    simpa [prefixWord, tailWord_5223880, baseEnd_5223880] using wordTrace_append hprefix tailTrace_5223880
  have hstable : (prefixWord ++ tailWord_5223880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5223880).length < 2 ^ (prefixWord ++ tailWord_5223880).sum := by decide
  have hdescent : baseEnd_5223880 < baseStart_5223880 := by decide
  rcases family_descends (prefixWord ++ tailWord_5223880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5223883 : List Nat := [1, 1, 1, 1, 3, 3, 2, 1, 3, 7]
def baseStart_5223883 : Nat := 118140960795 + 5223883 * 2 ^ 59
def prefixEnd_5223883 : Nat := 4983230072969 + 3 ^ 40 * 5223883 * 2
def baseEnd_5223883 : Nat := 894120953950363422479435

theorem tailTrace_5223883 : CollatzResearch.WordTrace tailWord_5223883 prefixEnd_5223883 894120953950363422479435 := by
  unfold tailWord_5223883
  simp only [CollatzResearch.WordTrace]
  refine ⟨190530665733771534032372303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127020443822514356021581535 190530665733771534032372303)
  ·
    refine ⟨285795998600657301048558455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190530665733771534032372303 285795998600657301048558455)
    ·
      refine ⟨428693997900985951572837683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285795998600657301048558455 428693997900985951572837683)
      ·
        refine ⟨643040996851478927359256525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 428693997900985951572837683 643040996851478927359256525)
        ·
          refine ⟨241140373819304597759721197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 643040996851478927359256525 241140373819304597759721197)
          ·
            refine ⟨90427640182239224159895449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 241140373819304597759721197 90427640182239224159895449)
            ·
              refine ⟨67820730136679418119921587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90427640182239224159895449 67820730136679418119921587)
              ·
                refine ⟨101731095205019127179882381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67820730136679418119921587 101731095205019127179882381)
                ·
                  refine ⟨38149160701882172692455893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101731095205019127179882381 38149160701882172692455893)
                  ·
                    refine ⟨894120953950363422479435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38149160701882172692455893 894120953950363422479435)
                    ·
                      rfl

theorem cell23_5223883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 7].length) (baseStart_5223883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5223883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5223883 prefixEnd_5223883 := by exact prefixLift 5223883
  have htrace : WordTrace (prefixWord ++ tailWord_5223883) baseStart_5223883 baseEnd_5223883 := by
    simpa [prefixWord, tailWord_5223883, baseEnd_5223883] using wordTrace_append hprefix tailTrace_5223883
  have hstable : (prefixWord ++ tailWord_5223883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5223883).length < 2 ^ (prefixWord ++ tailWord_5223883).sum := by decide
  have hdescent : baseEnd_5223883 < baseStart_5223883 := by decide
  rcases family_descends (prefixWord ++ tailWord_5223883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5223913 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 4, 8]
def baseStart_5223913 : Nat := 118140960795 + 5223913 * 2 ^ 59
def prefixEnd_5223913 : Nat := 4983230072969 + 3 ^ 40 * 5223913 * 2
def baseEnd_5223913 : Nat := 894126088756908383354389

theorem tailTrace_5223913 : CollatzResearch.WordTrace tailWord_5223913 prefixEnd_5223913 894126088756908383354389 := by
  unfold tailWord_5223913
  simp only [CollatzResearch.WordTrace]
  refine ⟨190531759923662849155964393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127021173282441899437309595 190531759923662849155964393)
  ·
    refine ⟨142898819942747136866973295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190531759923662849155964393 142898819942747136866973295)
    ·
      refine ⟨214348229914120705300459943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142898819942747136866973295 214348229914120705300459943)
      ·
        refine ⟨321522344871181057950689915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214348229914120705300459943 321522344871181057950689915)
        ·
          refine ⟨482283517306771586926034873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 321522344871181057950689915 482283517306771586926034873)
          ·
            refine ⟨361712637980078690194526155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 482283517306771586926034873 361712637980078690194526155)
            ·
              refine ⟨542568956970118035291789233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 361712637980078690194526155 542568956970118035291789233)
              ·
                refine ⟨406926717727588526468841925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 542568956970118035291789233 406926717727588526468841925)
                ·
                  refine ⟨76298759573922848712907861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 406926717727588526468841925 76298759573922848712907861)
                  ·
                    refine ⟨894126088756908383354389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 76298759573922848712907861 894126088756908383354389)
                    ·
                      rfl

theorem cell23_5223913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 8].length) (baseStart_5223913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5223913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5223913 prefixEnd_5223913 := by exact prefixLift 5223913
  have htrace : WordTrace (prefixWord ++ tailWord_5223913) baseStart_5223913 baseEnd_5223913 := by
    simpa [prefixWord, tailWord_5223913, baseEnd_5223913] using wordTrace_append hprefix tailTrace_5223913
  have hstable : (prefixWord ++ tailWord_5223913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5223913).length < 2 ^ (prefixWord ++ tailWord_5223913).sum := by decide
  have hdescent : baseEnd_5223913 < baseStart_5223913 := by decide
  rcases family_descends (prefixWord ++ tailWord_5223913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5223957 : List Nat := [1, 3, 2, 1, 3, 3, 1, 1, 1, 4, 3]
def baseStart_5223957 : Nat := 118140960795 + 5223957 * 2 ^ 59
def prefixEnd_5223957 : Nat := 4983230072969 + 3 ^ 40 * 5223957 * 2
def baseEnd_5223957 : Nat := 2682400859419522977912965

theorem tailTrace_5223957 : CollatzResearch.WordTrace tailWord_5223957 prefixEnd_5223957 2682400859419522977912965 := by
  unfold tailWord_5223957
  simp only [CollatzResearch.WordTrace]
  refine ⟨190533364735503444670566125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127022243157002296447044083 190533364735503444670566125)
  ·
    refine ⟨71450011775813791751462297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190533364735503444670566125 71450011775813791751462297)
    ·
      refine ⟨53587508831860343813596723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71450011775813791751462297 53587508831860343813596723)
      ·
        refine ⟨80381263247790515720395085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53587508831860343813596723 80381263247790515720395085)
        ·
          refine ⟨30142973717921443395148157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80381263247790515720395085 30142973717921443395148157)
          ·
            refine ⟨11303615144220541273180559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30142973717921443395148157 11303615144220541273180559)
            ·
              refine ⟨16955422716330811909770839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11303615144220541273180559 16955422716330811909770839)
              ·
                refine ⟨25433134074496217864656259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16955422716330811909770839 25433134074496217864656259)
                ·
                  refine ⟨38149701111744326796984389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25433134074496217864656259 38149701111744326796984389)
                  ·
                    refine ⟨7153068958452061274434573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38149701111744326796984389 7153068958452061274434573)
                    ·
                      refine ⟨2682400859419522977912965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7153068958452061274434573 2682400859419522977912965)
                      ·
                        rfl

theorem cell23_5223957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 4, 3].length) (baseStart_5223957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5223957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5223957 prefixEnd_5223957 := by exact prefixLift 5223957
  have htrace : WordTrace (prefixWord ++ tailWord_5223957) baseStart_5223957 baseEnd_5223957 := by
    simpa [prefixWord, tailWord_5223957, baseEnd_5223957] using wordTrace_append hprefix tailTrace_5223957
  have hstable : (prefixWord ++ tailWord_5223957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5223957).length < 2 ^ (prefixWord ++ tailWord_5223957).sum := by decide
  have hdescent : baseEnd_5223957 < baseStart_5223957 := by decide
  rcases family_descends (prefixWord ++ tailWord_5223957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5224014 : List Nat := [4, 1, 1, 1, 1, 2, 1, 5, 2, 3, 2]
def baseStart_5224014 : Nat := 118140960795 + 5224014 * 2 ^ 59
def prefixEnd_5224014 : Nat := 4983230072969 + 3 ^ 40 * 5224014 * 2
def baseEnd_5224014 : Nat := 2682430127816829254900203

theorem tailTrace_5224014 : CollatzResearch.WordTrace tailWord_5224014 prefixEnd_5224014 2682430127816829254900203 := by
  unfold tailWord_5224014
  simp only [CollatzResearch.WordTrace]
  refine ⟨23816930462037117925673887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127023629130864628936927397 23816930462037117925673887)
  ·
    refine ⟨35725395693055676888510831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23816930462037117925673887 35725395693055676888510831)
    ·
      refine ⟨53588093539583515332766247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35725395693055676888510831 53588093539583515332766247)
      ·
        refine ⟨80382140309375272999149371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53588093539583515332766247 80382140309375272999149371)
        ·
          refine ⟨120573210464062909498724057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80382140309375272999149371 120573210464062909498724057)
          ·
            refine ⟨90429907848047182124043043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120573210464062909498724057 90429907848047182124043043)
            ·
              refine ⟨135644861772070773186064565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90429907848047182124043043 135644861772070773186064565)
              ·
                refine ⟨12716705791131634986193553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 135644861772070773186064565 12716705791131634986193553)
                ·
                  refine ⟨9537529343348726239645165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12716705791131634986193553 9537529343348726239645165)
                  ·
                    refine ⟨3576573503755772339866937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9537529343348726239645165 3576573503755772339866937)
                    ·
                      refine ⟨2682430127816829254900203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3576573503755772339866937 2682430127816829254900203)
                      ·
                        rfl

theorem cell23_5224014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 5, 2, 3, 2].length) (baseStart_5224014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5224014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5224014 prefixEnd_5224014 := by exact prefixLift 5224014
  have htrace : WordTrace (prefixWord ++ tailWord_5224014) baseStart_5224014 baseEnd_5224014 := by
    simpa [prefixWord, tailWord_5224014, baseEnd_5224014] using wordTrace_append hprefix tailTrace_5224014
  have hstable : (prefixWord ++ tailWord_5224014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5224014).length < 2 ^ (prefixWord ++ tailWord_5224014).sum := by decide
  have hdescent : baseEnd_5224014 < baseStart_5224014 := by decide
  rcases family_descends (prefixWord ++ tailWord_5224014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5224047 : List Nat := [1, 1, 2, 1, 3, 2, 1, 4, 3, 2, 3]
def baseStart_5224047 : Nat := 118140960795 + 5224047 * 2 ^ 59
def prefixEnd_5224047 : Nat := 4983230072969 + 3 ^ 40 * 5224047 * 2
def baseEnd_5224047 : Nat := 2682447072678427625787551

theorem tailTrace_5224047 : CollatzResearch.WordTrace tailWord_5224047 prefixEnd_5224047 2682447072678427625787551 := by
  unfold tailWord_5224047
  simp only [CollatzResearch.WordTrace]
  refine ⟨190536647305177390041342395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127024431536784926694228263 190536647305177390041342395)
  ·
    refine ⟨285804970957766085062013593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190536647305177390041342395 285804970957766085062013593)
    ·
      refine ⟨214353728218324563796510195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 285804970957766085062013593 214353728218324563796510195)
      ·
        refine ⟨321530592327486845694765293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214353728218324563796510195 321530592327486845694765293)
        ·
          refine ⟨120573972122807567135536985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 321530592327486845694765293 120573972122807567135536985)
          ·
            refine ⟨90430479092105675351652739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120573972122807567135536985 90430479092105675351652739)
            ·
              refine ⟨135645718638158513027479109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90430479092105675351652739 135645718638158513027479109)
              ·
                refine ⟨25433572244654721192652333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 135645718638158513027479109 25433572244654721192652333)
                ·
                  refine ⟨9537589591745520447244625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25433572244654721192652333 9537589591745520447244625)
                  ·
                    refine ⟨7153192193809140335433469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9537589591745520447244625 7153192193809140335433469)
                    ·
                      refine ⟨2682447072678427625787551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7153192193809140335433469 2682447072678427625787551)
                      ·
                        rfl

theorem cell23_5224047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 3, 2, 3].length) (baseStart_5224047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5224047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5224047 prefixEnd_5224047 := by exact prefixLift 5224047
  have htrace : WordTrace (prefixWord ++ tailWord_5224047) baseStart_5224047 baseEnd_5224047 := by
    simpa [prefixWord, tailWord_5224047, baseEnd_5224047] using wordTrace_append hprefix tailTrace_5224047
  have hstable : (prefixWord ++ tailWord_5224047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5224047).length < 2 ^ (prefixWord ++ tailWord_5224047).sum := by decide
  have hdescent : baseEnd_5224047 < baseStart_5224047 := by decide
  rcases family_descends (prefixWord ++ tailWord_5224047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5224057 : List Nat := [1, 2, 1, 3, 3, 1, 2, 3, 1, 2, 4]
def baseStart_5224057 : Nat := 118140960795 + 5224057 * 2 ^ 59
def prefixEnd_5224057 : Nat := 4983230072969 + 3 ^ 40 * 5224057 * 2
def baseEnd_5224057 : Nat := 2682452207484972586662505

theorem tailTrace_5224057 : CollatzResearch.WordTrace tailWord_5224057 prefixEnd_5224057 2682452207484972586662505 := by
  unfold tailWord_5224057
  simp only [CollatzResearch.WordTrace]
  refine ⟨190537012035141161749206425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127024674690094107832804283 190537012035141161749206425)
  ·
    refine ⟨142902759026355871311904819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190537012035141161749206425 142902759026355871311904819)
    ·
      refine ⟨214354138539533806967857229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142902759026355871311904819 214354138539533806967857229)
      ·
        refine ⟨80382801952325177612946461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 214354138539533806967857229 80382801952325177612946461)
        ·
          refine ⟨30143550732121941604854923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80382801952325177612946461 30143550732121941604854923)
          ·
            refine ⟨45215326098182912407282385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30143550732121941604854923 45215326098182912407282385)
            ·
              refine ⟨33911494573637184305461789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45215326098182912407282385 33911494573637184305461789)
              ·
                refine ⟨12716810465113944114548171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33911494573637184305461789 12716810465113944114548171)
                ·
                  refine ⟨19075215697670916171822257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12716810465113944114548171 19075215697670916171822257)
                  ·
                    refine ⟨14306411773253187128866693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19075215697670916171822257 14306411773253187128866693)
                    ·
                      refine ⟨2682452207484972586662505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14306411773253187128866693 2682452207484972586662505)
                      ·
                        rfl

theorem cell23_5224057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 3, 1, 2, 4].length) (baseStart_5224057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5224057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5224057 prefixEnd_5224057 := by exact prefixLift 5224057
  have htrace : WordTrace (prefixWord ++ tailWord_5224057) baseStart_5224057 baseEnd_5224057 := by
    simpa [prefixWord, tailWord_5224057, baseEnd_5224057] using wordTrace_append hprefix tailTrace_5224057
  have hstable : (prefixWord ++ tailWord_5224057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5224057).length < 2 ^ (prefixWord ++ tailWord_5224057).sum := by decide
  have hdescent : baseEnd_5224057 < baseStart_5224057 := by decide
  rcases family_descends (prefixWord ++ tailWord_5224057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5224061 : List Nat := [1, 4, 1, 1, 4, 3, 1, 2, 1, 1, 4]
def baseStart_5224061 : Nat := 118140960795 + 5224061 * 2 ^ 59
def prefixEnd_5224061 : Nat := 4983230072969 + 3 ^ 40 * 5224061 * 2
def baseEnd_5224061 : Nat := 2682454261407590571012487

theorem tailTrace_5224061 : CollatzResearch.WordTrace tailWord_5224061 prefixEnd_5224061 2682454261407590571012487 := by
  unfold tailWord_5224061
  simp only [CollatzResearch.WordTrace]
  refine ⟨190537157927126670432352037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127024771951417780288234691 190537157927126670432352037)
  ·
    refine ⟨35725717111336250706066007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 190537157927126670432352037 35725717111336250706066007)
    ·
      refine ⟨53588575667004376059099011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35725717111336250706066007 53588575667004376059099011)
      ·
        refine ⟨80382863500506564088648517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53588575667004376059099011 80382863500506564088648517)
        ·
          refine ⟨15071786906344980766621597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80382863500506564088648517 15071786906344980766621597)
          ·
            refine ⟨5651920089879367787483099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15071786906344980766621597 5651920089879367787483099)
            ·
              refine ⟨8477880134819051681224649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5651920089879367787483099 8477880134819051681224649)
              ·
                refine ⟨6358410101114288760918487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8477880134819051681224649 6358410101114288760918487)
                ·
                  refine ⟨9537615151671433141377731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6358410101114288760918487 9537615151671433141377731)
                  ·
                    refine ⟨14306422727507149712066597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9537615151671433141377731 14306422727507149712066597)
                    ·
                      refine ⟨2682454261407590571012487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14306422727507149712066597 2682454261407590571012487)
                      ·
                        rfl

theorem cell23_5224061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 2, 1, 1, 4].length) (baseStart_5224061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5224061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5224061 prefixEnd_5224061 := by exact prefixLift 5224061
  have htrace : WordTrace (prefixWord ++ tailWord_5224061) baseStart_5224061 baseEnd_5224061 := by
    simpa [prefixWord, tailWord_5224061, baseEnd_5224061] using wordTrace_append hprefix tailTrace_5224061
  have hstable : (prefixWord ++ tailWord_5224061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5224061).length < 2 ^ (prefixWord ++ tailWord_5224061).sum := by decide
  have hdescent : baseEnd_5224061 < baseStart_5224061 := by decide
  rcases family_descends (prefixWord ++ tailWord_5224061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5224074 : List Nat := [3, 1, 2, 3, 2, 2, 1, 2, 1, 2, 4]
def baseStart_5224074 : Nat := 118140960795 + 5224074 * 2 ^ 59
def prefixEnd_5224074 : Nat := 4983230072969 + 3 ^ 40 * 5224074 * 2
def baseEnd_5224074 : Nat := 2682460936656099020149927

theorem tailTrace_5224074 : CollatzResearch.WordTrace tailWord_5224074 prefixEnd_5224074 2682460936656099020149927 := by
  unfold tailWord_5224074
  simp only [CollatzResearch.WordTrace]
  refine ⟨47634408019019893413143819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127025088050719715768383517 47634408019019893413143819)
  ·
    refine ⟨71451612028529840119715729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47634408019019893413143819 71451612028529840119715729)
    ·
      refine ⟨53588709021397380089786797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71451612028529840119715729 53588709021397380089786797)
      ·
        refine ⟨20095765883024017533670049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53588709021397380089786797 20095765883024017533670049)
        ·
          refine ⟨15071824412268013150252537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20095765883024017533670049 15071824412268013150252537)
          ·
            refine ⟨11303868309201009862689403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15071824412268013150252537 11303868309201009862689403)
            ·
              refine ⟨16955802463801514794034105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11303868309201009862689403 16955802463801514794034105)
              ·
                refine ⟨12716851847851136095525579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16955802463801514794034105 12716851847851136095525579)
                ·
                  refine ⟨19075277771776704143288369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12716851847851136095525579 19075277771776704143288369)
                  ·
                    refine ⟨14306458328832528107466277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19075277771776704143288369 14306458328832528107466277)
                    ·
                      refine ⟨2682460936656099020149927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14306458328832528107466277 2682460936656099020149927)
                      ·
                        rfl

theorem cell23_5224074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_5224074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5224074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5224074 prefixEnd_5224074 := by exact prefixLift 5224074
  have htrace : WordTrace (prefixWord ++ tailWord_5224074) baseStart_5224074 baseEnd_5224074 := by
    simpa [prefixWord, tailWord_5224074, baseEnd_5224074] using wordTrace_append hprefix tailTrace_5224074
  have hstable : (prefixWord ++ tailWord_5224074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5224074).length < 2 ^ (prefixWord ++ tailWord_5224074).sum := by decide
  have hdescent : baseEnd_5224074 < baseStart_5224074 := by decide
  rcases family_descends (prefixWord ++ tailWord_5224074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5224080 : List Nat := [2, 1, 1, 1, 1, 1, 3, 2, 4, 7]
def baseStart_5224080 : Nat := 118140960795 + 5224080 * 2 ^ 59
def prefixEnd_5224080 : Nat := 4983230072969 + 3 ^ 40 * 5224080 * 2
def baseEnd_5224080 : Nat := 894154672513341998891633

theorem tailTrace_5224080 : CollatzResearch.WordTrace tailWord_5224080 prefixEnd_5224080 894154672513341998891633 := by
  unfold tailWord_5224080
  simp only [CollatzResearch.WordTrace]
  refine ⟨95268925457028918338646847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127025233942705224451529129 95268925457028918338646847)
  ·
    refine ⟨142903388185543377507970271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95268925457028918338646847 142903388185543377507970271)
    ·
      refine ⟨214355082278315066261955407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142903388185543377507970271 214355082278315066261955407)
      ·
        refine ⟨321532623417472599392933111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214355082278315066261955407 321532623417472599392933111)
        ·
          refine ⟨482298935126208899089399667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 321532623417472599392933111 482298935126208899089399667)
          ·
            refine ⟨723448402689313348634099501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 482298935126208899089399667 723448402689313348634099501)
            ·
              refine ⟨271293151008492505737787313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 723448402689313348634099501 271293151008492505737787313)
              ·
                refine ⟨203469863256369379303340485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 271293151008492505737787313 203469863256369379303340485)
                ·
                  refine ⟨38150599360569258619376341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 203469863256369379303340485 38150599360569258619376341)
                  ·
                    refine ⟨894154672513341998891633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38150599360569258619376341 894154672513341998891633)
                    ·
                      rfl

theorem cell23_5224080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 4, 7].length) (baseStart_5224080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5224080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5224080 prefixEnd_5224080 := by exact prefixLift 5224080
  have htrace : WordTrace (prefixWord ++ tailWord_5224080) baseStart_5224080 baseEnd_5224080 := by
    simpa [prefixWord, tailWord_5224080, baseEnd_5224080] using wordTrace_append hprefix tailTrace_5224080
  have hstable : (prefixWord ++ tailWord_5224080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5224080).length < 2 ^ (prefixWord ++ tailWord_5224080).sum := by decide
  have hdescent : baseEnd_5224080 < baseStart_5224080 := by decide
  rcases family_descends (prefixWord ++ tailWord_5224080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5224084 : List Nat := [2, 4, 2, 2, 3, 10]
def baseStart_5224084 : Nat := 118140960795 + 5224084 * 2 ^ 59
def prefixEnd_5224084 : Nat := 4983230072969 + 3 ^ 40 * 5224084 * 2
def baseEnd_5224084 : Nat := 11038955026595242720267

theorem tailTrace_5224084 : CollatzResearch.WordTrace tailWord_5224084 prefixEnd_5224084 11038955026595242720267 := by
  unfold tailWord_5224084
  simp only [CollatzResearch.WordTrace]
  refine ⟨95268998403021672680219653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127025331204028896906959537 95268998403021672680219653)
  ·
    refine ⟨17862937200566563627541185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95268998403021672680219653 17862937200566563627541185)
    ·
      refine ⟨13397202900424922720655889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17862937200566563627541185 13397202900424922720655889)
      ·
        refine ⟨10047902175318692040491917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13397202900424922720655889 10047902175318692040491917)
        ·
          refine ⟨3767963315744509515184469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10047902175318692040491917 3767963315744509515184469)
          ·
            refine ⟨11038955026595242720267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3767963315744509515184469 11038955026595242720267)
            ·
              rfl

theorem cell23_5224084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 10].length) (baseStart_5224084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5224084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5224084 prefixEnd_5224084 := by exact prefixLift 5224084
  have htrace : WordTrace (prefixWord ++ tailWord_5224084) baseStart_5224084 baseEnd_5224084 := by
    simpa [prefixWord, tailWord_5224084, baseEnd_5224084] using wordTrace_append hprefix tailTrace_5224084
  have hstable : (prefixWord ++ tailWord_5224084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5224084).length < 2 ^ (prefixWord ++ tailWord_5224084).sum := by decide
  have hdescent : baseEnd_5224084 < baseStart_5224084 := by decide
  rcases family_descends (prefixWord ++ tailWord_5224084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5224097 : List Nat := [1, 2, 3, 3, 2, 1, 1, 1, 2, 7]
def baseStart_5224097 : Nat := 118140960795 + 5224097 * 2 ^ 59
def prefixEnd_5224097 : Nat := 4983230072969 + 3 ^ 40 * 5224097 * 2
def baseEnd_5224097 : Nat := 894157582237050810054107

theorem tailTrace_5224097 : CollatzResearch.WordTrace tailWord_5224097 prefixEnd_5224097 894157582237050810054107 := by
  unfold tailWord_5224097
  simp only [CollatzResearch.WordTrace]
  refine ⟨190538470954996248580662545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127025647303330832387108363 190538470954996248580662545)
  ·
    refine ⟨142903853216247186435496909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190538470954996248580662545 142903853216247186435496909)
    ·
      refine ⟨53588944956092694913311341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142903853216247186435496909 53588944956092694913311341)
      ·
        refine ⟨20095854358534760592491753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53588944956092694913311341 20095854358534760592491753)
        ·
          refine ⟨15071890768901070444368815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20095854358534760592491753 15071890768901070444368815)
          ·
            refine ⟨22607836153351605666553223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15071890768901070444368815 22607836153351605666553223)
            ·
              refine ⟨33911754230027408499829835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22607836153351605666553223 33911754230027408499829835)
              ·
                refine ⟨50867631345041112749744753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33911754230027408499829835 50867631345041112749744753)
                ·
                  refine ⟨38150723508780834562308565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50867631345041112749744753 38150723508780834562308565)
                  ·
                    refine ⟨894157582237050810054107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38150723508780834562308565 894157582237050810054107)
                    ·
                      rfl

theorem cell23_5224097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 7].length) (baseStart_5224097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5224097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5224097 prefixEnd_5224097 := by exact prefixLift 5224097
  have htrace : WordTrace (prefixWord ++ tailWord_5224097) baseStart_5224097 baseEnd_5224097 := by
    simpa [prefixWord, tailWord_5224097, baseEnd_5224097] using wordTrace_append hprefix tailTrace_5224097
  have hstable : (prefixWord ++ tailWord_5224097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5224097).length < 2 ^ (prefixWord ++ tailWord_5224097).sum := by decide
  have hdescent : baseEnd_5224097 < baseStart_5224097 := by decide
  rcases family_descends (prefixWord ++ tailWord_5224097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5224138 : List Nat := [3, 1, 2, 1, 5, 1, 1, 3, 1, 3, 2]
def baseStart_5224138 : Nat := 118140960795 + 5224138 * 2 ^ 59
def prefixEnd_5224138 : Nat := 4983230072969 + 3 ^ 40 * 5224138 * 2
def baseEnd_5224138 : Nat := 2682493799417986769749633

theorem tailTrace_5224138 : CollatzResearch.WordTrace tailWord_5224138 prefixEnd_5224138 2682493799417986769749633 := by
  unfold tailWord_5224138
  simp only [CollatzResearch.WordTrace]
  refine ⟨47634991586961928145726267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127026644231898475055270045 47634991586961928145726267)
  ·
    refine ⟨71452487380442892218589401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47634991586961928145726267 71452487380442892218589401)
    ·
      refine ⟨53589365535332169163942051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71452487380442892218589401 53589365535332169163942051)
      ·
        refine ⟨80384048302998253745913077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53589365535332169163942051 80384048302998253745913077)
        ·
          refine ⟨7536004528406086288679351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 80384048302998253745913077 7536004528406086288679351)
          ·
            refine ⟨11304006792609129433019027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7536004528406086288679351 11304006792609129433019027)
            ·
              refine ⟨16956010188913694149528541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11304006792609129433019027 16956010188913694149528541)
              ·
                refine ⟨6358503820842635306073203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16956010188913694149528541 6358503820842635306073203)
                ·
                  refine ⟨9537755731263952959109805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6358503820842635306073203 9537755731263952959109805)
                  ·
                    refine ⟨3576658399223982359666177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9537755731263952959109805 3576658399223982359666177)
                    ·
                      refine ⟨2682493799417986769749633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3576658399223982359666177 2682493799417986769749633)
                      ·
                        rfl

theorem cell23_5224138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 3, 1, 3, 2].length) (baseStart_5224138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5224138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5224138 prefixEnd_5224138 := by exact prefixLift 5224138
  have htrace : WordTrace (prefixWord ++ tailWord_5224138) baseStart_5224138 baseEnd_5224138 := by
    simpa [prefixWord, tailWord_5224138, baseEnd_5224138] using wordTrace_append hprefix tailTrace_5224138
  have hstable : (prefixWord ++ tailWord_5224138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5224138).length < 2 ^ (prefixWord ++ tailWord_5224138).sum := by decide
  have hdescent : baseEnd_5224138 < baseStart_5224138 := by decide
  rcases family_descends (prefixWord ++ tailWord_5224138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5224151 : List Nat := [1, 1, 3, 2, 1, 3, 3, 1, 4, 2, 2]
def baseStart_5224151 : Nat := 118140960795 + 5224151 * 2 ^ 59
def prefixEnd_5224151 : Nat := 4983230072969 + 3 ^ 40 * 5224151 * 2
def baseEnd_5224151 : Nat := 2682500474666495218887073

theorem tailTrace_5224151 : CollatzResearch.WordTrace tailWord_5224151 prefixEnd_5224151 2682500474666495218887073 := by
  unfold tailWord_5224151
  simp only [CollatzResearch.WordTrace]
  refine ⟨190540440496800615803128307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127026960331200410535418871 190540440496800615803128307)
  ·
    refine ⟨285810660745200923704692461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190540440496800615803128307 285810660745200923704692461)
    ·
      refine ⟨107178997779450346389259673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 285810660745200923704692461 107178997779450346389259673)
      ·
        refine ⟨80384248334587759791944755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107178997779450346389259673 80384248334587759791944755)
        ·
          refine ⟨120576372501881639687917133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80384248334587759791944755 120576372501881639687917133)
          ·
            refine ⟨45216139688205614882968925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120576372501881639687917133 45216139688205614882968925)
            ·
              refine ⟨16956052383077105581113347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45216139688205614882968925 16956052383077105581113347)
              ·
                refine ⟨25434078574615658371670021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16956052383077105581113347 25434078574615658371670021)
                ·
                  refine ⟨4768889732740435944688129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25434078574615658371670021 4768889732740435944688129)
                  ·
                    refine ⟨3576667299555326958516097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4768889732740435944688129 3576667299555326958516097)
                    ·
                      refine ⟨2682500474666495218887073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3576667299555326958516097 2682500474666495218887073)
                      ·
                        rfl

theorem cell23_5224151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 1, 4, 2, 2].length) (baseStart_5224151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5224151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5224151 prefixEnd_5224151 := by exact prefixLift 5224151
  have htrace : WordTrace (prefixWord ++ tailWord_5224151) baseStart_5224151 baseEnd_5224151 := by
    simpa [prefixWord, tailWord_5224151, baseEnd_5224151] using wordTrace_append hprefix tailTrace_5224151
  have hstable : (prefixWord ++ tailWord_5224151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5224151).length < 2 ^ (prefixWord ++ tailWord_5224151).sum := by decide
  have hdescent : baseEnd_5224151 < baseStart_5224151 := by decide
  rcases family_descends (prefixWord ++ tailWord_5224151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5224168 : List Nat := [2, 1, 4, 1, 3, 3, 1, 1, 1, 4, 2]
def baseStart_5224168 : Nat := 118140960795 + 5224168 * 2 ^ 59
def prefixEnd_5224168 : Nat := 4983230072969 + 3 ^ 40 * 5224168 * 2
def baseEnd_5224168 : Nat := 2682509203837621652374495

theorem tailTrace_5224168 : CollatzResearch.WordTrace tailWord_5224168 prefixEnd_5224168 2682509203837621652374495 := by
  unfold tailWord_5224168
  simp only [CollatzResearch.WordTrace]
  refine ⟨95270530268869513853248579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127027373691826018470998105 95270530268869513853248579)
  ·
    refine ⟨142905795403304270779872869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95270530268869513853248579 142905795403304270779872869)
    ·
      refine ⟨26794836638119550771226163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 142905795403304270779872869 26794836638119550771226163)
      ·
        refine ⟨40192254957179326156839245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26794836638119550771226163 40192254957179326156839245)
        ·
          refine ⟨15072095608942247308814717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40192254957179326156839245 15072095608942247308814717)
          ·
            refine ⟨5652035853353342740805519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15072095608942247308814717 5652035853353342740805519)
            ·
              refine ⟨8478053780030014111208279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5652035853353342740805519 8478053780030014111208279)
              ·
                refine ⟨12717080670045021166812419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8478053780030014111208279 12717080670045021166812419)
                ·
                  refine ⟨19075621005067531750218629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12717080670045021166812419 19075621005067531750218629)
                  ·
                    refine ⟨3576678938450162203165993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19075621005067531750218629 3576678938450162203165993)
                    ·
                      refine ⟨2682509203837621652374495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3576678938450162203165993 2682509203837621652374495)
                      ·
                        rfl

theorem cell23_5224168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 1, 1, 4, 2].length) (baseStart_5224168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5224168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5224168 prefixEnd_5224168 := by exact prefixLift 5224168
  have htrace : WordTrace (prefixWord ++ tailWord_5224168) baseStart_5224168 baseEnd_5224168 := by
    simpa [prefixWord, tailWord_5224168, baseEnd_5224168] using wordTrace_append hprefix tailTrace_5224168
  have hstable : (prefixWord ++ tailWord_5224168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5224168).length < 2 ^ (prefixWord ++ tailWord_5224168).sum := by decide
  have hdescent : baseEnd_5224168 < baseStart_5224168 := by decide
  rcases family_descends (prefixWord ++ tailWord_5224168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5224207 : List Nat := [1, 1, 2, 1, 1, 1, 4, 2, 3, 3, 4]
def baseStart_5224207 : Nat := 118140960795 + 5224207 * 2 ^ 59
def prefixEnd_5224207 : Nat := 4983230072969 + 3 ^ 40 * 5224207 * 2
def baseEnd_5224207 : Nat := 2682529229583146999786815

theorem tailTrace_5224207 : CollatzResearch.WordTrace tailWord_5224207 prefixEnd_5224207 2682529229583146999786815 := by
  unfold tailWord_5224207
  simp only [CollatzResearch.WordTrace]
  refine ⟨190542482984597737367166875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127028321989731824911444583 190542482984597737367166875)
  ·
    refine ⟨285813724476896606050750313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190542482984597737367166875 285813724476896606050750313)
    ·
      refine ⟨214360293357672454538062735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 285813724476896606050750313 214360293357672454538062735)
      ·
        refine ⟨321540440036508681807094103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214360293357672454538062735 321540440036508681807094103)
        ·
          refine ⟨482310660054763022710641155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 321540440036508681807094103 482310660054763022710641155)
          ·
            refine ⟨723465990082144534065961733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 482310660054763022710641155 723465990082144534065961733)
            ·
              refine ⟨135649873140402100137367825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 723465990082144534065961733 135649873140402100137367825)
              ·
                refine ⟨101737404855301575103025869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 135649873140402100137367825 101737404855301575103025869)
                ·
                  refine ⟨38151526820738090663634701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101737404855301575103025869 38151526820738090663634701)
                  ·
                    refine ⟨14306822557776783998863013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38151526820738090663634701 14306822557776783998863013)
                    ·
                      refine ⟨2682529229583146999786815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14306822557776783998863013 2682529229583146999786815)
                      ·
                        rfl

theorem cell23_5224207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 3, 4].length) (baseStart_5224207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5224207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5224207 prefixEnd_5224207 := by exact prefixLift 5224207
  have htrace : WordTrace (prefixWord ++ tailWord_5224207) baseStart_5224207 baseEnd_5224207 := by
    simpa [prefixWord, tailWord_5224207, baseEnd_5224207] using wordTrace_append hprefix tailTrace_5224207
  have hstable : (prefixWord ++ tailWord_5224207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5224207).length < 2 ^ (prefixWord ++ tailWord_5224207).sum := by decide
  have hdescent : baseEnd_5224207 < baseStart_5224207 := by decide
  rcases family_descends (prefixWord ++ tailWord_5224207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5224224 : List Nat := [2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 4]
def baseStart_5224224 : Nat := 118140960795 + 5224224 * 2 ^ 59
def prefixEnd_5224224 : Nat := 4983230072969 + 3 ^ 40 * 5224224 * 2
def baseEnd_5224224 : Nat := 2682537958754273433274237

theorem tailTrace_5224224 : CollatzResearch.WordTrace tailWord_5224224 prefixEnd_5224224 2682537958754273433274237 := by
  unfold tailWord_5224224
  simp only [CollatzResearch.WordTrace]
  refine ⟨95271551512768074635267863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127028735350357432847023817 95271551512768074635267863)
  ·
    refine ⟨142907327269152111952901795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95271551512768074635267863 142907327269152111952901795)
    ·
      refine ⟨214360990903728167929352693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142907327269152111952901795 214360990903728167929352693)
      ·
        refine ⟨20096342897224515743376815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 214360990903728167929352693 20096342897224515743376815)
        ·
          refine ⟨30144514345836773615065223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20096342897224515743376815 30144514345836773615065223)
          ·
            refine ⟨45216771518755160422597835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30144514345836773615065223 45216771518755160422597835)
            ·
              refine ⟨67825157278132740633896753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45216771518755160422597835 67825157278132740633896753)
              ·
                refine ⟨50868867958599555475422565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67825157278132740633896753 50868867958599555475422565)
                ·
                  refine ⟨9537912742237416651641731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50868867958599555475422565 9537912742237416651641731)
                  ·
                    refine ⟨14306869113356124977462597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9537912742237416651641731 14306869113356124977462597)
                    ·
                      refine ⟨2682537958754273433274237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14306869113356124977462597 2682537958754273433274237)
                      ·
                        rfl

theorem cell23_5224224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_5224224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5224224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5224224 prefixEnd_5224224 := by exact prefixLift 5224224
  have htrace : WordTrace (prefixWord ++ tailWord_5224224) baseStart_5224224 baseEnd_5224224 := by
    simpa [prefixWord, tailWord_5224224, baseEnd_5224224] using wordTrace_append hprefix tailTrace_5224224
  have hstable : (prefixWord ++ tailWord_5224224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5224224).length < 2 ^ (prefixWord ++ tailWord_5224224).sum := by decide
  have hdescent : baseEnd_5224224 < baseStart_5224224 := by decide
  rcases family_descends (prefixWord ++ tailWord_5224224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5224238 : List Nat := [4, 1, 3, 2, 2, 1, 2, 1, 2, 5]
def baseStart_5224238 : Nat := 118140960795 + 5224238 * 2 ^ 59
def prefixEnd_5224238 : Nat := 4983230072969 + 3 ^ 40 * 5224238 * 2
def baseEnd_5224238 : Nat := 894181715827812126166391

theorem tailTrace_5224238 : CollatzResearch.WordTrace tailWord_5224238 prefixEnd_5224238 894181715827812126166391 := by
  unfold tailWord_5224238
  simp only [CollatzResearch.WordTrace]
  refine ⟨23817951705935678707693171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127029075764990286441030245 23817951705935678707693171)
  ·
    refine ⟨35726927558903518061539757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23817951705935678707693171 35726927558903518061539757)
    ·
      refine ⟨13397597834588819273077409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35726927558903518061539757 13397597834588819273077409)
      ·
        refine ⟨10048198375941614454808057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13397597834588819273077409 10048198375941614454808057)
        ·
          refine ⟨7536148781956210841106043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10048198375941614454808057 7536148781956210841106043)
          ·
            refine ⟨11304223172934316261659065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7536148781956210841106043 11304223172934316261659065)
            ·
              refine ⟨8478167379700737196244299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11304223172934316261659065 8478167379700737196244299)
              ·
                refine ⟨12717251069551105794366449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8478167379700737196244299 12717251069551105794366449)
                ·
                  refine ⟨9537938302163329345774837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12717251069551105794366449 9537938302163329345774837)
                  ·
                    refine ⟨894181715827812126166391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9537938302163329345774837 894181715827812126166391)
                    ·
                      rfl

theorem cell23_5224238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_5224238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5224238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5224238 prefixEnd_5224238 := by exact prefixLift 5224238
  have htrace : WordTrace (prefixWord ++ tailWord_5224238) baseStart_5224238 baseEnd_5224238 := by
    simpa [prefixWord, tailWord_5224238, baseEnd_5224238] using wordTrace_append hprefix tailTrace_5224238
  have hstable : (prefixWord ++ tailWord_5224238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5224238).length < 2 ^ (prefixWord ++ tailWord_5224238).sum := by decide
  have hdescent : baseEnd_5224238 < baseStart_5224238 := by decide
  rcases family_descends (prefixWord ++ tailWord_5224238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5224241 : List Nat := [1, 2, 2, 3, 2, 3, 2, 1, 2, 1, 4]
def baseStart_5224241 : Nat := 118140960795 + 5224241 * 2 ^ 59
def prefixEnd_5224241 : Nat := 4983230072969 + 3 ^ 40 * 5224241 * 2
def baseEnd_5224241 : Nat := 2682546687925399866761659

theorem tailTrace_5224241 : CollatzResearch.WordTrace tailWord_5224241 prefixEnd_5224241 2682546687925399866761659 := by
  unfold tailWord_5224241
  simp only [CollatzResearch.WordTrace]
  refine ⟨190543723066474561173904577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127029148710983040782603051 190543723066474561173904577)
  ·
    refine ⟨142907792299855920880428433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190543723066474561173904577 142907792299855920880428433)
    ·
      refine ⟨107180844224891940660321325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142907792299855920880428433 107180844224891940660321325)
      ·
        refine ⟨40192816584334477747620497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107180844224891940660321325 40192816584334477747620497)
        ·
          refine ⟨30144612438250858310715373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40192816584334477747620497 30144612438250858310715373)
          ·
            refine ⟨11304229664344071866518265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30144612438250858310715373 11304229664344071866518265)
            ·
              refine ⟨8478172248258053899888699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11304229664344071866518265 8478172248258053899888699)
              ·
                refine ⟨12717258372387080849833049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8478172248258053899888699 12717258372387080849833049)
                ·
                  refine ⟨9537943779290310637374787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12717258372387080849833049 9537943779290310637374787)
                  ·
                    refine ⟨14306915668935465956062181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9537943779290310637374787 14306915668935465956062181)
                    ·
                      refine ⟨2682546687925399866761659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14306915668935465956062181 2682546687925399866761659)
                      ·
                        rfl

theorem cell23_5224241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 1, 2, 1, 4].length) (baseStart_5224241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5224241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5224241 prefixEnd_5224241 := by exact prefixLift 5224241
  have htrace : WordTrace (prefixWord ++ tailWord_5224241) baseStart_5224241 baseEnd_5224241 := by
    simpa [prefixWord, tailWord_5224241, baseEnd_5224241] using wordTrace_append hprefix tailTrace_5224241
  have hstable : (prefixWord ++ tailWord_5224241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5224241).length < 2 ^ (prefixWord ++ tailWord_5224241).sum := by decide
  have hdescent : baseEnd_5224241 < baseStart_5224241 := by decide
  rcases family_descends (prefixWord ++ tailWord_5224241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5224247 : List Nat := [1, 1, 3, 1, 2, 1, 2, 4, 8]
def baseStart_5224247 : Nat := 118140960795 + 5224247 * 2 ^ 59
def prefixEnd_5224247 : Nat := 4983230072969 + 3 ^ 40 * 5224247 * 2
def baseEnd_5224247 : Nat := 298061085423258538142959

theorem tailTrace_5224247 : CollatzResearch.WordTrace tailWord_5224247 prefixEnd_5224247 298061085423258538142959 := by
  unfold tailWord_5224247
  simp only [CollatzResearch.WordTrace]
  refine ⟨190543941904452824198622995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127029294602968549465748663 190543941904452824198622995)
  ·
    refine ⟨285815912856679236297934493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190543941904452824198622995 285815912856679236297934493)
    ·
      refine ⟨107180967321254713611725435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 285815912856679236297934493 107180967321254713611725435)
      ·
        refine ⟨160771450981882070417588153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107180967321254713611725435 160771450981882070417588153)
        ·
          refine ⟨120578588236411552813191115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160771450981882070417588153 120578588236411552813191115)
          ·
            refine ⟨180867882354617329219786673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120578588236411552813191115 180867882354617329219786673)
            ·
              refine ⟨135650911765962996914840005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 180867882354617329219786673 135650911765962996914840005)
              ·
                refine ⟨25434545956118061921532501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 135650911765962996914840005 25434545956118061921532501)
                ·
                  refine ⟨298061085423258538142959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25434545956118061921532501 298061085423258538142959)
                  ·
                    rfl

theorem cell23_5224247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 8].length) (baseStart_5224247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5224247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5224247 prefixEnd_5224247 := by exact prefixLift 5224247
  have htrace : WordTrace (prefixWord ++ tailWord_5224247) baseStart_5224247 baseEnd_5224247 := by
    simpa [prefixWord, tailWord_5224247, baseEnd_5224247] using wordTrace_append hprefix tailTrace_5224247
  have hstable : (prefixWord ++ tailWord_5224247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5224247).length < 2 ^ (prefixWord ++ tailWord_5224247).sum := by decide
  have hdescent : baseEnd_5224247 < baseStart_5224247 := by decide
  rcases family_descends (prefixWord ++ tailWord_5224247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5224264 : List Nat := [2, 1, 3, 1, 1, 4, 1, 4, 6]
def baseStart_5224264 : Nat := 118140960795 + 5224264 * 2 ^ 59
def prefixEnd_5224264 : Nat := 4983230072969 + 3 ^ 40 * 5224264 * 2
def baseEnd_5224264 : Nat := 298062055331161475197117

theorem tailTrace_5224264 : CollatzResearch.WordTrace tailWord_5224264 prefixEnd_5224264 298062055331161475197117 := by
  unfold tailWord_5224264
  simp only [CollatzResearch.WordTrace]
  refine ⟨95272280972695618050995923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127029707963594157401327897 95272280972695618050995923)
  ·
    refine ⟨142908421459043427076493885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95272280972695618050995923 142908421459043427076493885)
    ·
      refine ⟨53590658047141285153685207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142908421459043427076493885 53590658047141285153685207)
      ·
        refine ⟨80385987070711927730527811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53590658047141285153685207 80385987070711927730527811)
        ·
          refine ⟨120578980606067891595791717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80385987070711927730527811 120578980606067891595791717)
          ·
            refine ⟨22608558863637729674210947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 120578980606067891595791717 22608558863637729674210947)
            ·
              refine ⟨33912838295456594511316421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22608558863637729674210947 33912838295456594511316421)
              ·
                refine ⟨6358657180398111470871829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33912838295456594511316421 6358657180398111470871829)
                ·
                  refine ⟨298062055331161475197117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6358657180398111470871829 298062055331161475197117)
                  ·
                    rfl

theorem cell23_5224264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 4, 6].length) (baseStart_5224264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5224264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5224264 prefixEnd_5224264 := by exact prefixLift 5224264
  have htrace : WordTrace (prefixWord ++ tailWord_5224264) baseStart_5224264 baseEnd_5224264 := by
    simpa [prefixWord, tailWord_5224264, baseEnd_5224264] using wordTrace_append hprefix tailTrace_5224264
  have hstable : (prefixWord ++ tailWord_5224264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5224264).length < 2 ^ (prefixWord ++ tailWord_5224264).sum := by decide
  have hdescent : baseEnd_5224264 < baseStart_5224264 := by decide
  rcases family_descends (prefixWord ++ tailWord_5224264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5224324 : List Nat := [2, 3, 2, 1, 1, 1, 2, 2, 3, 6]
def baseStart_5224324 : Nat := 118140960795 + 5224324 * 2 ^ 59
def prefixEnd_5224324 : Nat := 4983230072969 + 3 ^ 40 * 5224324 * 2
def baseEnd_5224324 : Nat := 894196435606574347341259

theorem tailTrace_5224324 : CollatzResearch.WordTrace tailWord_5224324 prefixEnd_5224324 894196435606574347341259 := by
  unfold tailWord_5224324
  simp only [CollatzResearch.WordTrace]
  refine ⟨95273375162586933174588013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127031166883449244232784017 95273375162586933174588013)
  ·
    refine ⟨35727515685970099940470505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95273375162586933174588013 35727515685970099940470505)
    ·
      refine ⟨26795636764477574955352879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35727515685970099940470505 26795636764477574955352879)
      ·
        refine ⟨40193455146716362433029319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26795636764477574955352879 40193455146716362433029319)
        ·
          refine ⟨60290182720074543649543979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40193455146716362433029319 60290182720074543649543979)
          ·
            refine ⟨90435274080111815474315969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60290182720074543649543979 90435274080111815474315969)
            ·
              refine ⟨67826455560083861605736977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90435274080111815474315969 67826455560083861605736977)
              ·
                refine ⟨50869841670062896204302733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67826455560083861605736977 50869841670062896204302733)
                ·
                  refine ⟨19076190626273586076613525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50869841670062896204302733 19076190626273586076613525)
                  ·
                    refine ⟨894196435606574347341259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19076190626273586076613525 894196435606574347341259)
                    ·
                      rfl

theorem cell23_5224324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_5224324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5224324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5224324 prefixEnd_5224324 := by exact prefixLift 5224324
  have htrace : WordTrace (prefixWord ++ tailWord_5224324) baseStart_5224324 baseEnd_5224324 := by
    simpa [prefixWord, tailWord_5224324, baseEnd_5224324] using wordTrace_append hprefix tailTrace_5224324
  have hstable : (prefixWord ++ tailWord_5224324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5224324).length < 2 ^ (prefixWord ++ tailWord_5224324).sum := by decide
  have hdescent : baseEnd_5224324 < baseStart_5224324 := by decide
  rcases family_descends (prefixWord ++ tailWord_5224324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5224348 : List Nat := [2, 2, 3, 3, 1, 1, 1, 4, 1, 1, 4]
def baseStart_5224348 : Nat := 118140960795 + 5224348 * 2 ^ 59
def prefixEnd_5224348 : Nat := 4983230072969 + 3 ^ 40 * 5224348 * 2
def baseEnd_5224348 : Nat := 2682601630355430948123667

theorem tailTrace_5224348 : CollatzResearch.WordTrace tailWord_5224348 prefixEnd_5224348 2682601630355430948123667 := by
  unfold tailWord_5224348
  simp only [CollatzResearch.WordTrace]
  refine ⟨95273812838543459224024849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127031750451391278965366465 95273812838543459224024849)
  ·
    refine ⟨71455359628907594418018637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95273812838543459224024849 71455359628907594418018637)
    ·
      refine ⟨26795759860840347906756989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71455359628907594418018637 26795759860840347906756989)
      ·
        refine ⟨10048409947815130465033871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26795759860840347906756989 10048409947815130465033871)
        ·
          refine ⟨15072614921722695697550807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10048409947815130465033871 15072614921722695697550807)
          ·
            refine ⟨22608922382584043546326211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15072614921722695697550807 22608922382584043546326211)
            ·
              refine ⟨33913383573876065319489317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22608922382584043546326211 33913383573876065319489317)
              ·
                refine ⟨6358759420101762247404247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33913383573876065319489317 6358759420101762247404247)
                ·
                  refine ⟨9538139130152643371106371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6358759420101762247404247 9538139130152643371106371)
                  ·
                    refine ⟨14307208695228965056659557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9538139130152643371106371 14307208695228965056659557)
                    ·
                      refine ⟨2682601630355430948123667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14307208695228965056659557 2682601630355430948123667)
                      ·
                        rfl

theorem cell23_5224348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_5224348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5224348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5224348 prefixEnd_5224348 := by exact prefixLift 5224348
  have htrace : WordTrace (prefixWord ++ tailWord_5224348) baseStart_5224348 baseEnd_5224348 := by
    simpa [prefixWord, tailWord_5224348, baseEnd_5224348] using wordTrace_append hprefix tailTrace_5224348
  have hstable : (prefixWord ++ tailWord_5224348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5224348).length < 2 ^ (prefixWord ++ tailWord_5224348).sum := by decide
  have hdescent : baseEnd_5224348 < baseStart_5224348 := by decide
  rcases family_descends (prefixWord ++ tailWord_5224348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5224382 : List Nat := [4, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2]
def baseStart_5224382 : Nat := 118140960795 + 5224382 * 2 ^ 59
def prefixEnd_5224382 : Nat := 4983230072969 + 3 ^ 40 * 5224382 * 2
def baseEnd_5224382 : Nat := 2682619088697683815098511

theorem tailTrace_5224382 : CollatzResearch.WordTrace tailWord_5224382 prefixEnd_5224382 2682619088697683815098511 := by
  unfold tailWord_5224382
  simp only [CollatzResearch.WordTrace]
  refine ⟨23818608219870467781848425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127032577172642494836524933 23818608219870467781848425)
  ·
    refine ⟨17863956164902850836386319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23818608219870467781848425 17863956164902850836386319)
    ·
      refine ⟨26795934247354276254579479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17863956164902850836386319 26795934247354276254579479)
      ·
        refine ⟨40193901371031414381869219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26795934247354276254579479 40193901371031414381869219)
        ·
          refine ⟨60290852056547121572803829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40193901371031414381869219 60290852056547121572803829)
          ·
            refine ⟨5652267380301292647450359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60290852056547121572803829 5652267380301292647450359)
            ·
              refine ⟨8478401070451938971175539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5652267380301292647450359 8478401070451938971175539)
              ·
                refine ⟨12717601605677908456763309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8478401070451938971175539 12717601605677908456763309)
                ·
                  refine ⟨4769100602129215671286241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12717601605677908456763309 4769100602129215671286241)
                  ·
                    refine ⟨3576825451596911753464681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4769100602129215671286241 3576825451596911753464681)
                    ·
                      refine ⟨2682619088697683815098511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3576825451596911753464681 2682619088697683815098511)
                      ·
                        rfl

theorem cell23_5224382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2].length) (baseStart_5224382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5224382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5224382 prefixEnd_5224382 := by exact prefixLift 5224382
  have htrace : WordTrace (prefixWord ++ tailWord_5224382) baseStart_5224382 baseEnd_5224382 := by
    simpa [prefixWord, tailWord_5224382, baseEnd_5224382] using wordTrace_append hprefix tailTrace_5224382
  have hstable : (prefixWord ++ tailWord_5224382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5224382).length < 2 ^ (prefixWord ++ tailWord_5224382).sum := by decide
  have hdescent : baseEnd_5224382 < baseStart_5224382 := by decide
  rcases family_descends (prefixWord ++ tailWord_5224382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5224384 : List Nat := [2, 1, 1, 2, 3, 2, 2, 1, 2, 7]
def baseStart_5224384 : Nat := 118140960795 + 5224384 * 2 ^ 59
def prefixEnd_5224384 : Nat := 4983230072969 + 3 ^ 40 * 5224384 * 2
def baseEnd_5224384 : Nat := 894206705219664269091167

theorem tailTrace_5224384 : CollatzResearch.WordTrace tailWord_5224384 prefixEnd_5224384 894206705219664269091167 := by
  unfold tailWord_5224384
  simp only [CollatzResearch.WordTrace]
  refine ⟨95274469352478248298180103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127032625803304331064240137 95274469352478248298180103)
  ·
    refine ⟨142911704028717372447270155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95274469352478248298180103 142911704028717372447270155)
    ·
      refine ⟨214367556043076058670905233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142911704028717372447270155 214367556043076058670905233)
      ·
        refine ⟨160775667032307044003178925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214367556043076058670905233 160775667032307044003178925)
        ·
          refine ⟨60290875137115141501192097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 160775667032307044003178925 60290875137115141501192097)
          ·
            refine ⟨45218156352836356125894073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60290875137115141501192097 45218156352836356125894073)
            ·
              refine ⟨33913617264627267094420555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45218156352836356125894073 33913617264627267094420555)
              ·
                refine ⟨50870425896940900641630833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33913617264627267094420555 50870425896940900641630833)
                ·
                  refine ⟨38152819422705675481223125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50870425896940900641630833 38152819422705675481223125)
                  ·
                    refine ⟨894206705219664269091167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38152819422705675481223125 894206705219664269091167)
                    ·
                      rfl

theorem cell23_5224384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 2, 7].length) (baseStart_5224384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5224384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5224384 prefixEnd_5224384 := by exact prefixLift 5224384
  have htrace : WordTrace (prefixWord ++ tailWord_5224384) baseStart_5224384 baseEnd_5224384 := by
    simpa [prefixWord, tailWord_5224384, baseEnd_5224384] using wordTrace_append hprefix tailTrace_5224384
  have hstable : (prefixWord ++ tailWord_5224384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5224384).length < 2 ^ (prefixWord ++ tailWord_5224384).sum := by decide
  have hdescent : baseEnd_5224384 < baseStart_5224384 := by decide
  rcases family_descends (prefixWord ++ tailWord_5224384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5224391 : List Nat := [1, 1, 4, 1, 1, 2, 1, 1, 2, 7, 2]
def baseStart_5224391 : Nat := 118140960795 + 5224391 * 2 ^ 59
def prefixEnd_5224391 : Nat := 4983230072969 + 3 ^ 40 * 5224391 * 2
def baseEnd_5224391 : Nat := 2682623710023574279885969

theorem tailTrace_5224391 : CollatzResearch.WordTrace tailWord_5224391 prefixEnd_5224391 2682623710023574279885969 := by
  unfold tailWord_5224391
  simp only [CollatzResearch.WordTrace]
  refine ⟨190549194015931136791865027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127032796010620757861243351 190549194015931136791865027)
  ·
    refine ⟨285823791023896705187797541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190549194015931136791865027 285823791023896705187797541)
    ·
      refine ⟨53591960816980632222712039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 285823791023896705187797541 53591960816980632222712039)
      ·
        refine ⟨80387941225470948334068059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53591960816980632222712039 80387941225470948334068059)
        ·
          refine ⟨120581911838206422501102089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80387941225470948334068059 120581911838206422501102089)
          ·
            refine ⟨90436433878654816875826567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120581911838206422501102089 90436433878654816875826567)
            ·
              refine ⟨135654650817982225313739851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90436433878654816875826567 135654650817982225313739851)
              ·
                refine ⟨203481976226973337970609777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135654650817982225313739851 203481976226973337970609777)
                ·
                  refine ⟨152611482170230003477957333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 203481976226973337970609777 152611482170230003477957333)
                  ·
                    refine ⟨3576831613364765706514625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 152611482170230003477957333 3576831613364765706514625)
                    ·
                      refine ⟨2682623710023574279885969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3576831613364765706514625 2682623710023574279885969)
                      ·
                        rfl

theorem cell23_5224391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 7, 2].length) (baseStart_5224391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5224391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5224391 prefixEnd_5224391 := by exact prefixLift 5224391
  have htrace : WordTrace (prefixWord ++ tailWord_5224391) baseStart_5224391 baseEnd_5224391 := by
    simpa [prefixWord, tailWord_5224391, baseEnd_5224391] using wordTrace_append hprefix tailTrace_5224391
  have hstable : (prefixWord ++ tailWord_5224391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5224391).length < 2 ^ (prefixWord ++ tailWord_5224391).sum := by decide
  have hdescent : baseEnd_5224391 < baseStart_5224391 := by decide
  rcases family_descends (prefixWord ++ tailWord_5224391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5224402 : List Nat := [3, 2, 2, 3, 2, 2, 1, 2, 1, 2, 3]
def baseStart_5224402 : Nat := 118140960795 + 5224402 * 2 ^ 59
def prefixEnd_5224402 : Nat := 4983230072969 + 3 ^ 40 * 5224402 * 2
def baseEnd_5224402 : Nat := 2682629358310773736848419

theorem tailTrace_5224402 : CollatzResearch.WordTrace tailWord_5224402 prefixEnd_5224402 2682629358310773736848419 := by
  unfold tailWord_5224402
  simp only [CollatzResearch.WordTrace]
  refine ⟨47637398804722821417628865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127033063479260857113676973 47637398804722821417628865)
  ·
    refine ⟨35728049103542116063221649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47637398804722821417628865 35728049103542116063221649)
    ·
      refine ⟨26796036827656587047416237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35728049103542116063221649 26796036827656587047416237)
      ·
        refine ⟨10048513810371220142781089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26796036827656587047416237 10048513810371220142781089)
        ·
          refine ⟨7536385357778415107085817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10048513810371220142781089 7536385357778415107085817)
          ·
            refine ⟨5652289018333811330314363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7536385357778415107085817 5652289018333811330314363)
            ·
              refine ⟨8478433527500716995471545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5652289018333811330314363 8478433527500716995471545)
              ·
                refine ⟨6358825145625537746603659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8478433527500716995471545 6358825145625537746603659)
                ·
                  refine ⟨9538237718438306619905489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6358825145625537746603659 9538237718438306619905489)
                  ·
                    refine ⟨7153678288828729964929117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9538237718438306619905489 7153678288828729964929117)
                    ·
                      refine ⟨2682629358310773736848419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7153678288828729964929117 2682629358310773736848419)
                      ·
                        rfl

theorem cell23_5224402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_5224402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5224402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5224402 prefixEnd_5224402 := by exact prefixLift 5224402
  have htrace : WordTrace (prefixWord ++ tailWord_5224402) baseStart_5224402 baseEnd_5224402 := by
    simpa [prefixWord, tailWord_5224402, baseEnd_5224402] using wordTrace_append hprefix tailTrace_5224402
  have hstable : (prefixWord ++ tailWord_5224402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5224402).length < 2 ^ (prefixWord ++ tailWord_5224402).sum := by decide
  have hdescent : baseEnd_5224402 < baseStart_5224402 := by decide
  rcases family_descends (prefixWord ++ tailWord_5224402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5224408 : List Nat := [2, 1, 2, 2, 2, 2, 3, 1, 3, 3, 2]
def baseStart_5224408 : Nat := 118140960795 + 5224408 * 2 ^ 59
def prefixEnd_5224408 : Nat := 4983230072969 + 3 ^ 40 * 5224408 * 2
def baseEnd_5224408 : Nat := 2682632439194700713373391

theorem tailTrace_5224408 : CollatzResearch.WordTrace tailWord_5224408 prefixEnd_5224408 2682632439194700713373391 := by
  unfold tailWord_5224408
  simp only [CollatzResearch.WordTrace]
  refine ⟨95274907028434774347616939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127033209371246365796822585 95274907028434774347616939)
  ·
    refine ⟨142912360542652161521425409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95274907028434774347616939 142912360542652161521425409)
    ·
      refine ⟨107184270406989121141069057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142912360542652161521425409 107184270406989121141069057)
      ·
        refine ⟨80388202805241840855801793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107184270406989121141069057 80388202805241840855801793)
        ·
          refine ⟨60291152103931380641851345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80388202805241840855801793 60291152103931380641851345)
          ·
            refine ⟨45218364077948535481388509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60291152103931380641851345 45218364077948535481388509)
            ·
              refine ⟨16956886529230700805520691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45218364077948535481388509 16956886529230700805520691)
              ·
                refine ⟨25435329793846051208281037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16956886529230700805520691 25435329793846051208281037)
                ·
                  refine ⟨9538248672692269203105389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25435329793846051208281037 9538248672692269203105389)
                  ·
                    refine ⟨3576843252259600951164521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9538248672692269203105389 3576843252259600951164521)
                    ·
                      refine ⟨2682632439194700713373391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3576843252259600951164521 2682632439194700713373391)
                      ·
                        rfl

theorem cell23_5224408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 3, 3, 2].length) (baseStart_5224408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5224408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5224408 prefixEnd_5224408 := by exact prefixLift 5224408
  have htrace : WordTrace (prefixWord ++ tailWord_5224408) baseStart_5224408 baseEnd_5224408 := by
    simpa [prefixWord, tailWord_5224408, baseEnd_5224408] using wordTrace_append hprefix tailTrace_5224408
  have hstable : (prefixWord ++ tailWord_5224408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5224408).length < 2 ^ (prefixWord ++ tailWord_5224408).sum := by decide
  have hdescent : baseEnd_5224408 < baseStart_5224408 := by decide
  rcases family_descends (prefixWord ++ tailWord_5224408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5224412 : List Nat := [2, 2, 6, 1, 1, 1, 1, 2, 1, 2, 4]
def baseStart_5224412 : Nat := 118140960795 + 5224412 * 2 ^ 59
def prefixEnd_5224412 : Nat := 4983230072969 + 3 ^ 40 * 5224412 * 2
def baseEnd_5224412 : Nat := 2682634493117318697723373

theorem tailTrace_5224412 : CollatzResearch.WordTrace tailWord_5224412 prefixEnd_5224412 2682634493117318697723373 := by
  unfold tailWord_5224412
  simp only [CollatzResearch.WordTrace]
  refine ⟨95274979974427528689189745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127033306632570038252252993 95274979974427528689189745)
  ·
    refine ⟨71456234980820646516892309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95274979974427528689189745 71456234980820646516892309)
    ·
      refine ⟨3349511014725967805479327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 71456234980820646516892309 3349511014725967805479327)
      ·
        refine ⟨5024266522088951708218991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3349511014725967805479327 5024266522088951708218991)
        ·
          refine ⟨7536399783133427562328487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5024266522088951708218991 7536399783133427562328487)
          ·
            refine ⟨11304599674700141343492731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7536399783133427562328487 11304599674700141343492731)
            ·
              refine ⟨16956899512050212015239097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11304599674700141343492731 16956899512050212015239097)
              ·
                refine ⟨12717674634037659011429323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16956899512050212015239097 12717674634037659011429323)
                ·
                  refine ⟨19076511951056488517143985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12717674634037659011429323 19076511951056488517143985)
                  ·
                    refine ⟨14307383963292366387857989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19076511951056488517143985 14307383963292366387857989)
                    ·
                      refine ⟨2682634493117318697723373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14307383963292366387857989 2682634493117318697723373)
                      ·
                        rfl

theorem cell23_5224412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_5224412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5224412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5224412 prefixEnd_5224412 := by exact prefixLift 5224412
  have htrace : WordTrace (prefixWord ++ tailWord_5224412) baseStart_5224412 baseEnd_5224412 := by
    simpa [prefixWord, tailWord_5224412, baseEnd_5224412] using wordTrace_append hprefix tailTrace_5224412
  have hstable : (prefixWord ++ tailWord_5224412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5224412).length < 2 ^ (prefixWord ++ tailWord_5224412).sum := by decide
  have hdescent : baseEnd_5224412 < baseStart_5224412 := by decide
  rcases family_descends (prefixWord ++ tailWord_5224412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5224441 : List Nat := [1, 2, 1, 3, 1, 4, 1, 1, 2, 4, 3]
def baseStart_5224441 : Nat := 118140960795 + 5224441 * 2 ^ 59
def prefixEnd_5224441 : Nat := 4983230072969 + 3 ^ 40 * 5224441 * 2
def baseEnd_5224441 : Nat := 2682649384056299084260739

theorem tailTrace_5224441 : CollatzResearch.WordTrace tailWord_5224441 prefixEnd_5224441 2682649384056299084260739 := by
  unfold tailWord_5224441
  simp only [CollatzResearch.WordTrace]
  refine ⟨190551017665749995331185177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127034011777166663554123451 190551017665749995331185177)
  ·
    refine ⟨142913263249312496498388883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190551017665749995331185177 142913263249312496498388883)
    ·
      refine ⟨214369894873968744747583325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142913263249312496498388883 214369894873968744747583325)
      ·
        refine ⟨80388710577738279280343747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 214369894873968744747583325 80388710577738279280343747)
        ·
          refine ⟨120583065866607418920515621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80388710577738279280343747 120583065866607418920515621)
          ·
            refine ⟨22609324849988891047596679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 120583065866607418920515621 22609324849988891047596679)
            ·
              refine ⟨33913987274983336571395019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22609324849988891047596679 33913987274983336571395019)
              ·
                refine ⟨50870980912475004857092529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33913987274983336571395019 50870980912475004857092529)
                ·
                  refine ⟨38153235684356253642819397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50870980912475004857092529 38153235684356253642819397)
                  ·
                    refine ⟨7153731690816797558028637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38153235684356253642819397 7153731690816797558028637)
                    ·
                      refine ⟨2682649384056299084260739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7153731690816797558028637 2682649384056299084260739)
                      ·
                        rfl

theorem cell23_5224441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 4, 3].length) (baseStart_5224441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5224441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5224441 prefixEnd_5224441 := by exact prefixLift 5224441
  have htrace : WordTrace (prefixWord ++ tailWord_5224441) baseStart_5224441 baseEnd_5224441 := by
    simpa [prefixWord, tailWord_5224441, baseEnd_5224441] using wordTrace_append hprefix tailTrace_5224441
  have hstable : (prefixWord ++ tailWord_5224441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5224441).length < 2 ^ (prefixWord ++ tailWord_5224441).sum := by decide
  have hdescent : baseEnd_5224441 < baseStart_5224441 := by decide
  rcases family_descends (prefixWord ++ tailWord_5224441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5224455 : List Nat := [1, 1, 4, 3, 1, 3, 2, 1, 1, 4, 2]
def baseStart_5224455 : Nat := 118140960795 + 5224455 * 2 ^ 59
def prefixEnd_5224455 : Nat := 4983230072969 + 3 ^ 40 * 5224455 * 2
def baseEnd_5224455 : Nat := 2682656572785462029485675

theorem tailTrace_5224455 : CollatzResearch.WordTrace tailWord_5224455 prefixEnd_5224455 2682656572785462029485675 := by
  unfold tailWord_5224455
  simp only [CollatzResearch.WordTrace]
  refine ⟨190551528287699275722194819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127034352191799517148129879 190551528287699275722194819)
  ·
    refine ⟨285827292431548913583292229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190551528287699275722194819 285827292431548913583292229)
    ·
      refine ⟨53592617330915421296867293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 285827292431548913583292229 53592617330915421296867293)
      ·
        refine ⟨20097231499093282986325235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53592617330915421296867293 20097231499093282986325235)
        ·
          refine ⟨30145847248639924479487853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20097231499093282986325235 30145847248639924479487853)
          ·
            refine ⟨11304692718239971679807945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30145847248639924479487853 11304692718239971679807945)
            ·
              refine ⟨8478519538679978759855959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11304692718239971679807945 8478519538679978759855959)
              ·
                refine ⟨12717779308019968139783939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8478519538679978759855959 12717779308019968139783939)
                ·
                  refine ⟨19076668962029952209675909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12717779308019968139783939 19076668962029952209675909)
                  ·
                    refine ⟨3576875430380616039314233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19076668962029952209675909 3576875430380616039314233)
                    ·
                      refine ⟨2682656572785462029485675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3576875430380616039314233 2682656572785462029485675)
                      ·
                        rfl

theorem cell23_5224455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 1, 1, 4, 2].length) (baseStart_5224455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5224455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5224455 prefixEnd_5224455 := by exact prefixLift 5224455
  have htrace : WordTrace (prefixWord ++ tailWord_5224455) baseStart_5224455 baseEnd_5224455 := by
    simpa [prefixWord, tailWord_5224455, baseEnd_5224455] using wordTrace_append hprefix tailTrace_5224455
  have hstable : (prefixWord ++ tailWord_5224455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5224455).length < 2 ^ (prefixWord ++ tailWord_5224455).sum := by decide
  have hdescent : baseEnd_5224455 < baseStart_5224455 := by decide
  rcases family_descends (prefixWord ++ tailWord_5224455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5224464 : List Nat := [2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 8]
def baseStart_5224464 : Nat := 118140960795 + 5224464 * 2 ^ 59
def prefixEnd_5224464 : Nat := 4983230072969 + 3 ^ 40 * 5224464 * 2
def baseEnd_5224464 : Nat := 2682661194111352494273133

theorem tailTrace_5224464 : CollatzResearch.WordTrace tailWord_5224464 prefixEnd_5224464 2682661194111352494273133 := by
  unfold tailWord_5224464
  simp only [CollatzResearch.WordTrace]
  refine ⟨95275928272333335129636223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127034571029777780172848297 95275928272333335129636223)
  ·
    refine ⟨142913892408500002694454335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95275928272333335129636223 142913892408500002694454335)
    ·
      refine ⟨214370838612750004041681503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142913892408500002694454335 214370838612750004041681503)
      ·
        refine ⟨321556257919125006062522255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214370838612750004041681503 321556257919125006062522255)
        ·
          refine ⟨482334386878687509093783383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 321556257919125006062522255 482334386878687509093783383)
          ·
            refine ⟨723501580318031263640675075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 482334386878687509093783383 723501580318031263640675075)
            ·
              refine ⟨1085252370477046895461012613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 723501580318031263640675075 1085252370477046895461012613)
              ·
                refine ⟨203484819464446292898939865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1085252370477046895461012613 203484819464446292898939865)
                ·
                  refine ⟨152613614598334719674204899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 203484819464446292898939865 152613614598334719674204899)
                  ·
                    refine ⟨228920421897502079511307349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 152613614598334719674204899 228920421897502079511307349)
                    ·
                      refine ⟨2682661194111352494273133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 228920421897502079511307349 2682661194111352494273133)
                      ·
                        rfl

theorem cell23_5224464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 8].length) (baseStart_5224464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5224464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5224464 prefixEnd_5224464 := by exact prefixLift 5224464
  have htrace : WordTrace (prefixWord ++ tailWord_5224464) baseStart_5224464 baseEnd_5224464 := by
    simpa [prefixWord, tailWord_5224464, baseEnd_5224464] using wordTrace_append hprefix tailTrace_5224464
  have hstable : (prefixWord ++ tailWord_5224464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5224464).length < 2 ^ (prefixWord ++ tailWord_5224464).sum := by decide
  have hdescent : baseEnd_5224464 < baseStart_5224464 := by decide
  rcases family_descends (prefixWord ++ tailWord_5224464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5224501 : List Nat := [1, 3, 3, 1, 1, 1, 2, 3, 1, 2, 5]
def baseStart_5224501 : Nat := 118140960795 + 5224501 * 2 ^ 59
def prefixEnd_5224501 : Nat := 4983230072969 + 3 ^ 40 * 5224501 * 2
def baseEnd_5224501 : Nat := 2682680192895568849510463

theorem tailTrace_5224501 : CollatzResearch.WordTrace tailWord_5224501 prefixEnd_5224501 2682680192895568849510463 := by
  unfold tailWord_5224501
  simp only [CollatzResearch.WordTrace]
  refine ⟨190553206045532625578369357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127035470697021750385579571 190553206045532625578369357)
  ·
    refine ⟨71457452267074734591888509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190553206045532625578369357 71457452267074734591888509)
    ·
      refine ⟨26796544600153025471958191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71457452267074734591888509 26796544600153025471958191)
      ·
        refine ⟨40194816900229538207937287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26796544600153025471958191 40194816900229538207937287)
        ·
          refine ⟨60292225350344307311905931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40194816900229538207937287 60292225350344307311905931)
          ·
            refine ⟨90438338025516460967858897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60292225350344307311905931 90438338025516460967858897)
            ·
              refine ⟨67828753519137345725894173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90438338025516460967858897 67828753519137345725894173)
              ·
                refine ⟨25435782569676504647210315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67828753519137345725894173 25435782569676504647210315)
                ·
                  refine ⟨38153673854514756970815473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25435782569676504647210315 38153673854514756970815473)
                  ·
                    refine ⟨28615255390886067728111605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38153673854514756970815473 28615255390886067728111605)
                    ·
                      refine ⟨2682680192895568849510463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28615255390886067728111605 2682680192895568849510463)
                      ·
                        rfl

theorem cell23_5224501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_5224501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5224501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5224501 prefixEnd_5224501 := by exact prefixLift 5224501
  have htrace : WordTrace (prefixWord ++ tailWord_5224501) baseStart_5224501 baseEnd_5224501 := by
    simpa [prefixWord, tailWord_5224501, baseEnd_5224501] using wordTrace_append hprefix tailTrace_5224501
  have hstable : (prefixWord ++ tailWord_5224501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5224501).length < 2 ^ (prefixWord ++ tailWord_5224501).sum := by decide
  have hdescent : baseEnd_5224501 < baseStart_5224501 := by decide
  rcases family_descends (prefixWord ++ tailWord_5224501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5224511 : List Nat := [1, 1, 2, 2, 3, 1, 3, 2, 1, 3, 4]
def baseStart_5224511 : Nat := 118140960795 + 5224511 * 2 ^ 59
def prefixEnd_5224511 : Nat := 4983230072969 + 3 ^ 40 * 5224511 * 2
def baseEnd_5224511 : Nat := 2682685327702113810385417

theorem tailTrace_5224511 : CollatzResearch.WordTrace tailWord_5224511 prefixEnd_5224511 2682685327702113810385417 := by
  unfold tailWord_5224511
  simp only [CollatzResearch.WordTrace]
  refine ⟨190553570775496397286233387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127035713850330931524155591 190553570775496397286233387)
  ·
    refine ⟨285830356163244595929350081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190553570775496397286233387 285830356163244595929350081)
    ·
      refine ⟨214372767122433446947012561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 285830356163244595929350081 214372767122433446947012561)
      ·
        refine ⟨160779575341825085210259421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214372767122433446947012561 160779575341825085210259421)
        ·
          refine ⟨60292340753184406953847283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 160779575341825085210259421 60292340753184406953847283)
          ·
            refine ⟨90438511129776610430770925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60292340753184406953847283 90438511129776610430770925)
            ·
              refine ⟨33914441673666228911539097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90438511129776610430770925 33914441673666228911539097)
              ·
                refine ⟨25435831255249671683654323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33914441673666228911539097 25435831255249671683654323)
                ·
                  refine ⟨38153746882874507525481485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25435831255249671683654323 38153746882874507525481485)
                  ·
                    refine ⟨14307655081077940322055557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38153746882874507525481485 14307655081077940322055557)
                    ·
                      refine ⟨2682685327702113810385417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14307655081077940322055557 2682685327702113810385417)
                      ·
                        rfl

theorem cell23_5224511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 3, 4].length) (baseStart_5224511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5224511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5224511 prefixEnd_5224511 := by exact prefixLift 5224511
  have htrace : WordTrace (prefixWord ++ tailWord_5224511) baseStart_5224511 baseEnd_5224511 := by
    simpa [prefixWord, tailWord_5224511, baseEnd_5224511] using wordTrace_append hprefix tailTrace_5224511
  have hstable : (prefixWord ++ tailWord_5224511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5224511).length < 2 ^ (prefixWord ++ tailWord_5224511).sum := by decide
  have hdescent : baseEnd_5224511 < baseStart_5224511 := by decide
  rcases family_descends (prefixWord ++ tailWord_5224511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5224531 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 5, 4, 3]
def baseStart_5224531 : Nat := 118140960795 + 5224531 * 2 ^ 59
def prefixEnd_5224531 : Nat := 4983230072969 + 3 ^ 40 * 5224531 * 2
def baseEnd_5224531 : Nat := 2682695597315203732135325

theorem tailTrace_5224531 : CollatzResearch.WordTrace tailWord_5224531 prefixEnd_5224531 2682695597315203732135325 := by
  unfold tailWord_5224531
  simp only [CollatzResearch.WordTrace]
  refine ⟨190554300235423940701961447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127036200156949293801307631 190554300235423940701961447)
  ·
    refine ⟨285831450353135911052942171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190554300235423940701961447 285831450353135911052942171)
    ·
      refine ⟨428747175529703866579413257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285831450353135911052942171 428747175529703866579413257)
      ·
        refine ⟨321560381647277899934559943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 428747175529703866579413257 321560381647277899934559943)
        ·
          refine ⟨482340572470916849901839915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 321560381647277899934559943 482340572470916849901839915)
          ·
            refine ⟨723510858706375274852759873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 482340572470916849901839915 723510858706375274852759873)
            ·
              refine ⟨542633144029781456139569905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 723510858706375274852759873 542633144029781456139569905)
              ·
                refine ⟨406974858022336092104677429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 542633144029781456139569905 406974858022336092104677429)
                ·
                  refine ⟨38153892939594008634813509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 406974858022336092104677429 38153892939594008634813509)
                  ·
                    refine ⟨7153854926173876619027533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38153892939594008634813509 7153854926173876619027533)
                    ·
                      refine ⟨2682695597315203732135325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7153854926173876619027533 2682695597315203732135325)
                      ·
                        rfl

theorem cell23_5224531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 4, 3].length) (baseStart_5224531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5224531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5224531 prefixEnd_5224531 := by exact prefixLift 5224531
  have htrace : WordTrace (prefixWord ++ tailWord_5224531) baseStart_5224531 baseEnd_5224531 := by
    simpa [prefixWord, tailWord_5224531, baseEnd_5224531] using wordTrace_append hprefix tailTrace_5224531
  have hstable : (prefixWord ++ tailWord_5224531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5224531).length < 2 ^ (prefixWord ++ tailWord_5224531).sum := by decide
  have hdescent : baseEnd_5224531 < baseStart_5224531 := by decide
  rcases family_descends (prefixWord ++ tailWord_5224531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5224548 : List Nat := [2, 3, 1, 1, 2, 1, 3, 1, 4, 2, 3]
def baseStart_5224548 : Nat := 118140960795 + 5224548 * 2 ^ 59
def prefixEnd_5224548 : Nat := 4983230072969 + 3 ^ 40 * 5224548 * 2
def baseEnd_5224548 : Nat := 2682704326486330165622747

theorem tailTrace_5224548 : CollatzResearch.WordTrace tailWord_5224548 prefixEnd_5224548 2682704326486330165622747 := by
  unfold tailWord_5224548
  simp only [CollatzResearch.WordTrace]
  refine ⟨95277460138181176302665149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127036613517574901736886865 95277460138181176302665149)
  ·
    refine ⟨35729047551817941113499431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95277460138181176302665149 35729047551817941113499431)
    ·
      refine ⟨53593571327726911670249147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35729047551817941113499431 53593571327726911670249147)
      ·
        refine ⟨80390356991590367505373721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53593571327726911670249147 80390356991590367505373721)
        ·
          refine ⟨60292767743692775629030291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80390356991590367505373721 60292767743692775629030291)
          ·
            refine ⟨90439151615539163443545437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60292767743692775629030291 90439151615539163443545437)
            ·
              refine ⟨33914681855827186291329539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90439151615539163443545437 33914681855827186291329539)
              ·
                refine ⟨50872022783740779436994309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33914681855827186291329539 50872022783740779436994309)
                ·
                  refine ⟨9538504271951396144436433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50872022783740779436994309 9538504271951396144436433)
                  ·
                    refine ⟨7153878203963547108327325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9538504271951396144436433 7153878203963547108327325)
                    ·
                      refine ⟨2682704326486330165622747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7153878203963547108327325 2682704326486330165622747)
                      ·
                        rfl

theorem cell23_5224548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 4, 2, 3].length) (baseStart_5224548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5224548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5224548 prefixEnd_5224548 := by exact prefixLift 5224548
  have htrace : WordTrace (prefixWord ++ tailWord_5224548) baseStart_5224548 baseEnd_5224548 := by
    simpa [prefixWord, tailWord_5224548, baseEnd_5224548] using wordTrace_append hprefix tailTrace_5224548
  have hstable : (prefixWord ++ tailWord_5224548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5224548).length < 2 ^ (prefixWord ++ tailWord_5224548).sum := by decide
  have hdescent : baseEnd_5224548 < baseStart_5224548 := by decide
  rcases family_descends (prefixWord ++ tailWord_5224548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5224551 : List Nat := [1, 1, 5, 1, 1, 2, 1, 3, 8]
def baseStart_5224551 : Nat := 118140960795 + 5224551 * 2 ^ 59
def prefixEnd_5224551 : Nat := 4983230072969 + 3 ^ 40 * 5224551 * 2
def baseEnd_5224551 : Nat := 298078429658699294876137

theorem tailTrace_5224551 : CollatzResearch.WordTrace tailWord_5224551 prefixEnd_5224551 298078429658699294876137 := by
  unfold tailWord_5224551
  simp only [CollatzResearch.WordTrace]
  refine ⟨190555029695351484117689507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127036686463567656078459671 190555029695351484117689507)
  ·
    refine ⟨285832544543027226176534261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190555029695351484117689507 285832544543027226176534261)
    ·
      refine ⟨26796801050908802454050087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 285832544543027226176534261 26796801050908802454050087)
      ·
        refine ⟨40195201576363203681075131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26796801050908802454050087 40195201576363203681075131)
        ·
          refine ⟨60292802364544805521612697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40195201576363203681075131 60292802364544805521612697)
          ·
            refine ⟨45219601773408604141209523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60292802364544805521612697 45219601773408604141209523)
            ·
              refine ⟨67829402660112906211814285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45219601773408604141209523 67829402660112906211814285)
              ·
                refine ⟨25436025997542339829430357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67829402660112906211814285 25436025997542339829430357)
                ·
                  refine ⟨298078429658699294876137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25436025997542339829430357 298078429658699294876137)
                  ·
                    rfl

theorem cell23_5224551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 8].length) (baseStart_5224551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5224551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5224551 prefixEnd_5224551 := by exact prefixLift 5224551
  have htrace : WordTrace (prefixWord ++ tailWord_5224551) baseStart_5224551 baseEnd_5224551 := by
    simpa [prefixWord, tailWord_5224551, baseEnd_5224551] using wordTrace_append hprefix tailTrace_5224551
  have hstable : (prefixWord ++ tailWord_5224551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5224551).length < 2 ^ (prefixWord ++ tailWord_5224551).sum := by decide
  have hdescent : baseEnd_5224551 < baseStart_5224551 := by decide
  rcases family_descends (prefixWord ++ tailWord_5224551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5224629 : List Nat := [1, 3, 3, 4, 1, 1, 1, 2, 3, 1, 3]
def baseStart_5224629 : Nat := 118140960795 + 5224629 * 2 ^ 59
def prefixEnd_5224629 : Nat := 4983230072969 + 3 ^ 40 * 5224629 * 2
def baseEnd_5224629 : Nat := 2682745918419344348709875

theorem tailTrace_5224629 : CollatzResearch.WordTrace tailWord_5224629 prefixEnd_5224629 2682745918419344348709875 := by
  unfold tailWord_5224629
  simp only [CollatzResearch.WordTrace]
  refine ⟨190557874589068903439028941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127038583059379268959352627 190557874589068903439028941)
  ·
    refine ⟨71459202970900838789635853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190557874589068903439028941 71459202970900838789635853)
    ·
      refine ⟨26797201114087814546113445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71459202970900838789635853 26797201114087814546113445)
      ·
        refine ⟨5024475208891465227396271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26797201114087814546113445 5024475208891465227396271)
        ·
          refine ⟨7536712813337197841094407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5024475208891465227396271 7536712813337197841094407)
          ·
            refine ⟨11305069220005796761641611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7536712813337197841094407 11305069220005796761641611)
            ·
              refine ⟨16957603830008695142462417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11305069220005796761641611 16957603830008695142462417)
              ·
                refine ⟨12718202872506521356846813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16957603830008695142462417 12718202872506521356846813)
                ·
                  refine ⟨4769326077189945508817555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12718202872506521356846813 4769326077189945508817555)
                  ·
                    refine ⟨7153989115784918263226333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4769326077189945508817555 7153989115784918263226333)
                    ·
                      refine ⟨2682745918419344348709875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7153989115784918263226333 2682745918419344348709875)
                      ·
                        rfl

theorem cell23_5224629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_5224629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5224629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5224629 prefixEnd_5224629 := by exact prefixLift 5224629
  have htrace : WordTrace (prefixWord ++ tailWord_5224629) baseStart_5224629 baseEnd_5224629 := by
    simpa [prefixWord, tailWord_5224629, baseEnd_5224629] using wordTrace_append hprefix tailTrace_5224629
  have hstable : (prefixWord ++ tailWord_5224629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5224629).length < 2 ^ (prefixWord ++ tailWord_5224629).sum := by decide
  have hdescent : baseEnd_5224629 < baseStart_5224629 := by decide
  rcases family_descends (prefixWord ++ tailWord_5224629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5224655 : List Nat := [1, 1, 2, 1, 1, 3, 5, 3, 1, 2, 3]
def baseStart_5224655 : Nat := 118140960795 + 5224655 * 2 ^ 59
def prefixEnd_5224655 : Nat := 4983230072969 + 3 ^ 40 * 5224655 * 2
def baseEnd_5224655 : Nat := 2682759268916361246984755

theorem tailTrace_5224655 : CollatzResearch.WordTrace tailWord_5224655 prefixEnd_5224655 2682759268916361246984755 := by
  unfold tailWord_5224655
  simp only [CollatzResearch.WordTrace]
  refine ⟨190558822886974709879475419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127039215257983139919650279 190558822886974709879475419)
  ·
    refine ⟨285838234330462064819213129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190558822886974709879475419 285838234330462064819213129)
    ·
      refine ⟨214378675747846548614409847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 285838234330462064819213129 214378675747846548614409847)
      ·
        refine ⟨321568013621769822921614771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214378675747846548614409847 321568013621769822921614771)
        ·
          refine ⟨482352020432654734382422157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 321568013621769822921614771 482352020432654734382422157)
          ·
            refine ⟨180882007662245525393408309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 482352020432654734382422157 180882007662245525393408309)
            ·
              refine ⟨16957688218335518005632029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 180882007662245525393408309 16957688218335518005632029)
              ·
                refine ⟨6359133081875819252112011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16957688218335518005632029 6359133081875819252112011)
                ·
                  refine ⟨9538699622813728878168017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6359133081875819252112011 9538699622813728878168017)
                  ·
                    refine ⟨7154024717110296658626013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9538699622813728878168017 7154024717110296658626013)
                    ·
                      refine ⟨2682759268916361246984755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7154024717110296658626013 2682759268916361246984755)
                      ·
                        rfl

theorem cell23_5224655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 3, 1, 2, 3].length) (baseStart_5224655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5224655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5224655 prefixEnd_5224655 := by exact prefixLift 5224655
  have htrace : WordTrace (prefixWord ++ tailWord_5224655) baseStart_5224655 baseEnd_5224655 := by
    simpa [prefixWord, tailWord_5224655, baseEnd_5224655] using wordTrace_append hprefix tailTrace_5224655
  have hstable : (prefixWord ++ tailWord_5224655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5224655).length < 2 ^ (prefixWord ++ tailWord_5224655).sum := by decide
  have hdescent : baseEnd_5224655 < baseStart_5224655 := by decide
  rcases family_descends (prefixWord ++ tailWord_5224655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5224658 : List Nat := [3, 2, 2, 2, 1, 3, 10]
def baseStart_5224658 : Nat := 118140960795 + 5224658 * 2 ^ 59
def prefixEnd_5224658 : Nat := 4983230072969 + 3 ^ 40 * 5224658 * 2
def baseEnd_5224658 : Nat := 33120503819238576978361

theorem tailTrace_5224658 : CollatzResearch.WordTrace tailWord_5224658 prefixEnd_5224658 33120503819238576978361 := by
  unfold tailWord_5224658
  simp only [CollatzResearch.WordTrace]
  refine ⟨47639733076490960347958657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127039288203975894261223085 47639733076490960347958657)
  ·
    refine ⟨35729799807368220260968993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47639733076490960347958657 35729799807368220260968993)
    ·
      refine ⟨26797349855526165195726745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35729799807368220260968993 26797349855526165195726745)
      ·
        refine ⟨20098012391644623896795059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26797349855526165195726745 20098012391644623896795059)
        ·
          refine ⟨30147018587466935845192589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20098012391644623896795059 30147018587466935845192589)
          ·
            refine ⟨11305131970300100941947221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30147018587466935845192589 11305131970300100941947221)
            ·
              refine ⟨33120503819238576978361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11305131970300100941947221 33120503819238576978361)
              ·
                rfl

theorem cell23_5224658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 10].length) (baseStart_5224658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5224658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5224658 prefixEnd_5224658 := by exact prefixLift 5224658
  have htrace : WordTrace (prefixWord ++ tailWord_5224658) baseStart_5224658 baseEnd_5224658 := by
    simpa [prefixWord, tailWord_5224658, baseEnd_5224658] using wordTrace_append hprefix tailTrace_5224658
  have hstable : (prefixWord ++ tailWord_5224658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5224658).length < 2 ^ (prefixWord ++ tailWord_5224658).sum := by decide
  have hdescent : baseEnd_5224658 < baseStart_5224658 := by decide
  rcases family_descends (prefixWord ++ tailWord_5224658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5224669 : List Nat := [1, 4, 3, 2, 1, 1, 1, 3, 3, 2, 2]
def baseStart_5224669 : Nat := 118140960795 + 5224669 * 2 ^ 59
def prefixEnd_5224669 : Nat := 4983230072969 + 3 ^ 40 * 5224669 * 2
def baseEnd_5224669 : Nat := 2682766457645524192209691

theorem tailTrace_5224669 : CollatzResearch.WordTrace tailWord_5224669 prefixEnd_5224669 2682766457645524192209691 := by
  unfold tailWord_5224669
  simp only [CollatzResearch.WordTrace]
  refine ⟨190559333508923990270485061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127039555672615993513656707 190559333508923990270485061)
  ·
    refine ⟨35729875032923248175715949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 190559333508923990270485061 35729875032923248175715949)
    ·
      refine ⟨13398703137346218065893481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35729875032923248175715949 13398703137346218065893481)
      ·
        refine ⟨10049027353009663549420111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13398703137346218065893481 10049027353009663549420111)
        ·
          refine ⟨15073541029514495324130167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10049027353009663549420111 15073541029514495324130167)
          ·
            refine ⟨22610311544271742986195251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15073541029514495324130167 22610311544271742986195251)
            ·
              refine ⟨33915467316407614479292877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22610311544271742986195251 33915467316407614479292877)
              ·
                refine ⟨12718300243652855429734829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33915467316407614479292877 12718300243652855429734829)
                ·
                  refine ⟨4769362591369820786150561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12718300243652855429734829 4769362591369820786150561)
                  ·
                    refine ⟨3577021943527365589612921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4769362591369820786150561 3577021943527365589612921)
                    ·
                      refine ⟨2682766457645524192209691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3577021943527365589612921 2682766457645524192209691)
                      ·
                        rfl

theorem cell23_5224669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_5224669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5224669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5224669 prefixEnd_5224669 := by exact prefixLift 5224669
  have htrace : WordTrace (prefixWord ++ tailWord_5224669) baseStart_5224669 baseEnd_5224669 := by
    simpa [prefixWord, tailWord_5224669, baseEnd_5224669] using wordTrace_append hprefix tailTrace_5224669
  have hstable : (prefixWord ++ tailWord_5224669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5224669).length < 2 ^ (prefixWord ++ tailWord_5224669).sum := by decide
  have hdescent : baseEnd_5224669 < baseStart_5224669 := by decide
  rcases family_descends (prefixWord ++ tailWord_5224669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5224679 : List Nat := [1, 1, 5, 3, 1, 2, 3, 1, 2, 4]
def baseStart_5224679 : Nat := 118140960795 + 5224679 * 2 ^ 59
def prefixEnd_5224679 : Nat := 4983230072969 + 3 ^ 40 * 5224679 * 2
def baseEnd_5224679 : Nat := 894257197484023051028215

theorem tailTrace_5224679 : CollatzResearch.WordTrace tailWord_5224679 prefixEnd_5224679 894257197484023051028215 := by
  unfold tailWord_5224679
  simp only [CollatzResearch.WordTrace]
  refine ⟨190559698238887761978349091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127039798825925174652232727 190559698238887761978349091)
  ·
    refine ⟨285839547358331642967523637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190559698238887761978349091 285839547358331642967523637)
    ·
      refine ⟨26797457564843591528205341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 285839547358331642967523637 26797457564843591528205341)
      ·
        refine ⟨10049046586816346823077003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26797457564843591528205341 10049046586816346823077003)
        ·
          refine ⟨15073569880224520234615505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10049046586816346823077003 15073569880224520234615505)
          ·
            refine ⟨11305177410168390175961629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15073569880224520234615505 11305177410168390175961629)
            ·
              refine ⟨4239441528813146315985611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11305177410168390175961629 4239441528813146315985611)
              ·
                refine ⟨6359162293219719473978417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4239441528813146315985611 6359162293219719473978417)
                ·
                  refine ⟨4769371719914789605483813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6359162293219719473978417 4769371719914789605483813)
                  ·
                    refine ⟨894257197484023051028215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4769371719914789605483813 894257197484023051028215)
                    ·
                      rfl

theorem cell23_5224679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 3, 1, 2, 4].length) (baseStart_5224679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5224679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5224679 prefixEnd_5224679 := by exact prefixLift 5224679
  have htrace : WordTrace (prefixWord ++ tailWord_5224679) baseStart_5224679 baseEnd_5224679 := by
    simpa [prefixWord, tailWord_5224679, baseEnd_5224679] using wordTrace_append hprefix tailTrace_5224679
  have hstable : (prefixWord ++ tailWord_5224679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5224679).length < 2 ^ (prefixWord ++ tailWord_5224679).sum := by decide
  have hdescent : baseEnd_5224679 < baseStart_5224679 := by decide
  rcases family_descends (prefixWord ++ tailWord_5224679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5224698 : List Nat := [3, 1, 1, 1, 1, 5, 1, 1, 2, 2, 5]
def baseStart_5224698 : Nat := 118140960795 + 5224698 * 2 ^ 59
def prefixEnd_5224698 : Nat := 4983230072969 + 3 ^ 40 * 5224698 * 2
def baseEnd_5224698 : Nat := 2682781348584504578747057

theorem tailTrace_5224698 : CollatzResearch.WordTrace tailWord_5224698 prefixEnd_5224698 2682781348584504578747057 := by
  unfold tailWord_5224698
  simp only [CollatzResearch.WordTrace]
  refine ⟨47640097806454732055822687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127040260817212618815527165 47640097806454732055822687)
  ·
    refine ⟨71460146709682098083734031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47640097806454732055822687 71460146709682098083734031)
    ·
      refine ⟨107190220064523147125601047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71460146709682098083734031 107190220064523147125601047)
      ·
        refine ⟨160785330096784720688401571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107190220064523147125601047 160785330096784720688401571)
        ·
          refine ⟨241177995145177081032602357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160785330096784720688401571 241177995145177081032602357)
          ·
            refine ⟨22610437044860351346806471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 241177995145177081032602357 22610437044860351346806471)
            ·
              refine ⟨33915655567290527020209707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22610437044860351346806471 33915655567290527020209707)
              ·
                refine ⟨50873483350935790530314561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33915655567290527020209707 50873483350935790530314561)
                ·
                  refine ⟨38155112513201842897735921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50873483350935790530314561 38155112513201842897735921)
                  ·
                    refine ⟨28616334384901382173301941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38155112513201842897735921 28616334384901382173301941)
                    ·
                      refine ⟨2682781348584504578747057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28616334384901382173301941 2682781348584504578747057)
                      ·
                        rfl

theorem cell23_5224698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 2, 2, 5].length) (baseStart_5224698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5224698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5224698 prefixEnd_5224698 := by exact prefixLift 5224698
  have htrace : WordTrace (prefixWord ++ tailWord_5224698) baseStart_5224698 baseEnd_5224698 := by
    simpa [prefixWord, tailWord_5224698, baseEnd_5224698] using wordTrace_append hprefix tailTrace_5224698
  have hstable : (prefixWord ++ tailWord_5224698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5224698).length < 2 ^ (prefixWord ++ tailWord_5224698).sum := by decide
  have hdescent : baseEnd_5224698 < baseStart_5224698 := by decide
  rcases family_descends (prefixWord ++ tailWord_5224698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5224702 : List Nat := [4, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3]
def baseStart_5224702 : Nat := 118140960795 + 5224702 * 2 ^ 59
def prefixEnd_5224702 : Nat := 4983230072969 + 3 ^ 40 * 5224702 * 2
def baseEnd_5224702 : Nat := 2682783402507122563097039

theorem tailTrace_5224702 : CollatzResearch.WordTrace tailWord_5224702 prefixEnd_5224702 2682783402507122563097039 := by
  unfold tailWord_5224702
  simp only [CollatzResearch.WordTrace]
  refine ⟨23820067139725554613304545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 127040358078536291270957573 23820067139725554613304545)
  ·
    refine ⟨17865050354794165959978409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23820067139725554613304545 17865050354794165959978409)
    ·
      refine ⟨13398787766095624469983807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17865050354794165959978409 13398787766095624469983807)
      ·
        refine ⟨20098181649143436704975711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13398787766095624469983807 20098181649143436704975711)
        ·
          refine ⟨30147272473715155057463567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20098181649143436704975711 30147272473715155057463567)
          ·
            refine ⟨45220908710572732586195351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30147272473715155057463567 45220908710572732586195351)
            ·
              refine ⟨67831363065859098879293027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45220908710572732586195351 67831363065859098879293027)
              ·
                refine ⟨101747044598788648318939541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67831363065859098879293027 101747044598788648318939541)
                ·
                  refine ⟨4769392715568217889950291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 101747044598788648318939541 4769392715568217889950291)
                  ·
                    refine ⟨7154089073352326834925437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4769392715568217889950291 7154089073352326834925437)
                    ·
                      refine ⟨2682783402507122563097039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7154089073352326834925437 2682783402507122563097039)
                      ·
                        rfl

theorem cell23_5224702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_5224702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5224702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5224702 prefixEnd_5224702 := by exact prefixLift 5224702
  have htrace : WordTrace (prefixWord ++ tailWord_5224702) baseStart_5224702 baseEnd_5224702 := by
    simpa [prefixWord, tailWord_5224702, baseEnd_5224702] using wordTrace_append hprefix tailTrace_5224702
  have hstable : (prefixWord ++ tailWord_5224702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5224702).length < 2 ^ (prefixWord ++ tailWord_5224702).sum := by decide
  have hdescent : baseEnd_5224702 < baseStart_5224702 := by decide
  rcases family_descends (prefixWord ++ tailWord_5224702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5224728 : List Nat := [2, 1, 2, 3, 1, 2, 1, 2, 1, 3, 5]
def baseStart_5224728 : Nat := 118140960795 + 5224728 * 2 ^ 59
def prefixEnd_5224728 : Nat := 4983230072969 + 3 ^ 40 * 5224728 * 2
def baseEnd_5224728 : Nat := 2682796753004139461371919

theorem tailTrace_5224728 : CollatzResearch.WordTrace tailWord_5224728 prefixEnd_5224728 2682796753004139461371919 := by
  unfold tailWord_5224728
  simp only [CollatzResearch.WordTrace]
  refine ⟨95280742707855121673441419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127040990277140162231255225 95280742707855121673441419)
  ·
    refine ⟨142921114061782682510162129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95280742707855121673441419 142921114061782682510162129)
    ·
      refine ⟨107190835546337011882621597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142921114061782682510162129 107190835546337011882621597)
      ·
        refine ⟨40196563329876379455983099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107190835546337011882621597 40196563329876379455983099)
        ·
          refine ⟨60294844994814569183974649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40196563329876379455983099 60294844994814569183974649)
          ·
            refine ⟨45221133746110926887980987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60294844994814569183974649 45221133746110926887980987)
            ·
              refine ⟨67831700619166390331971481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45221133746110926887980987 67831700619166390331971481)
              ·
                refine ⟨50873775464374792748978611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67831700619166390331971481 50873775464374792748978611)
                ·
                  refine ⟨76310663196562189123467917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50873775464374792748978611 76310663196562189123467917)
                  ·
                    refine ⟨28616498698710820921300469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 76310663196562189123467917 28616498698710820921300469)
                    ·
                      refine ⟨2682796753004139461371919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28616498698710820921300469 2682796753004139461371919)
                      ·
                        rfl

theorem cell23_5224728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_5224728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5224728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5224728 prefixEnd_5224728 := by exact prefixLift 5224728
  have htrace : WordTrace (prefixWord ++ tailWord_5224728) baseStart_5224728 baseEnd_5224728 := by
    simpa [prefixWord, tailWord_5224728, baseEnd_5224728] using wordTrace_append hprefix tailTrace_5224728
  have hstable : (prefixWord ++ tailWord_5224728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5224728).length < 2 ^ (prefixWord ++ tailWord_5224728).sum := by decide
  have hdescent : baseEnd_5224728 < baseStart_5224728 := by decide
  rcases family_descends (prefixWord ++ tailWord_5224728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5224736 : List Nat := [2, 1, 1, 5, 2, 3, 2, 1, 2, 1, 3]
def baseStart_5224736 : Nat := 118140960795 + 5224736 * 2 ^ 59
def prefixEnd_5224736 : Nat := 4983230072969 + 3 ^ 40 * 5224736 * 2
def baseEnd_5224736 : Nat := 2682800860849375430071883

theorem tailTrace_5224736 : CollatzResearch.WordTrace tailWord_5224736 prefixEnd_5224736 2682800860849375430071883 := by
  unfold tailWord_5224736
  simp only [CollatzResearch.WordTrace]
  refine ⟨95280888599840630356587031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127041184799787507142116041 95280888599840630356587031)
  ·
    refine ⟨142921332899760945534880547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95280888599840630356587031 142921332899760945534880547)
    ·
      refine ⟨214381999349641418302320821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142921332899760945534880547 214381999349641418302320821)
      ·
        refine ⟨20098312439028882965842577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 214381999349641418302320821 20098312439028882965842577)
        ·
          refine ⟨15073734329271662224381933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20098312439028882965842577 15073734329271662224381933)
          ·
            refine ⟨5652650373476873334143225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15073734329271662224381933 5652650373476873334143225)
            ·
              refine ⟨4239487780107655000607419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5652650373476873334143225 4239487780107655000607419)
              ·
                refine ⟨6359231670161482500911129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4239487780107655000607419 6359231670161482500911129)
                ·
                  refine ⟨4769423752621111875683347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6359231670161482500911129 4769423752621111875683347)
                  ·
                    refine ⟨7154135628931667813525021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4769423752621111875683347 7154135628931667813525021)
                    ·
                      refine ⟨2682800860849375430071883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7154135628931667813525021 2682800860849375430071883)
                      ·
                        rfl

theorem cell23_5224736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 2, 1, 2, 1, 3].length) (baseStart_5224736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5224736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5224736 prefixEnd_5224736 := by exact prefixLift 5224736
  have htrace : WordTrace (prefixWord ++ tailWord_5224736) baseStart_5224736 baseEnd_5224736 := by
    simpa [prefixWord, tailWord_5224736, baseEnd_5224736] using wordTrace_append hprefix tailTrace_5224736
  have hstable : (prefixWord ++ tailWord_5224736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5224736).length < 2 ^ (prefixWord ++ tailWord_5224736).sum := by decide
  have hdescent : baseEnd_5224736 < baseStart_5224736 := by decide
  rcases family_descends (prefixWord ++ tailWord_5224736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5224748 : List Nat := [2, 2, 1, 1, 1, 3, 2, 4, 7]
def baseStart_5224748 : Nat := 118140960795 + 5224748 * 2 ^ 59
def prefixEnd_5224748 : Nat := 4983230072969 + 3 ^ 40 * 5224748 * 2
def baseEnd_5224748 : Nat := 298089669179692153680203

theorem tailTrace_5224748 : CollatzResearch.WordTrace tailWord_5224748 prefixEnd_5224748 298089669179692153680203 := by
  unfold tailWord_5224748
  simp only [CollatzResearch.WordTrace]
  refine ⟨95281107437818893381305449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127041476583758524508407265 95281107437818893381305449)
  ·
    refine ⟨71460830578364170035979087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95281107437818893381305449 71460830578364170035979087)
    ·
      refine ⟨107191245867546255053968631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71460830578364170035979087 107191245867546255053968631)
      ·
        refine ⟨160786868801319382580952947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107191245867546255053968631 160786868801319382580952947)
        ·
          refine ⟨241180303201979073871429421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160786868801319382580952947 241180303201979073871429421)
          ·
            refine ⟨90442613700742152701786033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 241180303201979073871429421 90442613700742152701786033)
            ·
              refine ⟨67831960275556614526339525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90442613700742152701786033 67831960275556614526339525)
              ·
                refine ⟨12718492551666865223688661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67831960275556614526339525 12718492551666865223688661)
                ·
                  refine ⟨298089669179692153680203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12718492551666865223688661 298089669179692153680203)
                  ·
                    rfl

theorem cell23_5224748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 7].length) (baseStart_5224748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5224748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5224748 prefixEnd_5224748 := by exact prefixLift 5224748
  have htrace : WordTrace (prefixWord ++ tailWord_5224748) baseStart_5224748 baseEnd_5224748 := by
    simpa [prefixWord, tailWord_5224748, baseEnd_5224748] using wordTrace_append hprefix tailTrace_5224748
  have hstable : (prefixWord ++ tailWord_5224748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5224748).length < 2 ^ (prefixWord ++ tailWord_5224748).sum := by decide
  have hdescent : baseEnd_5224748 < baseStart_5224748 := by decide
  rcases family_descends (prefixWord ++ tailWord_5224748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5224775 : List Nat := [1, 1, 4, 1, 2, 2, 2, 2, 2, 3, 3]
def baseStart_5224775 : Nat := 118140960795 + 5224775 * 2 ^ 59
def prefixEnd_5224775 : Nat := 4983230072969 + 3 ^ 40 * 5224775 * 2
def baseEnd_5224775 : Nat := 2682820886594900777484203

theorem tailTrace_5224775 : CollatzResearch.WordTrace tailWord_5224775 prefixEnd_5224775 2682820886594900777484203 := by
  unfold tailWord_5224775
  simp only [CollatzResearch.WordTrace]
  refine ⟨190563199646539970373843779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127042133097693313582562519 190563199646539970373843779)
  ·
    refine ⟨285844799469809955560765669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190563199646539970373843779 285844799469809955560765669)
    ·
      refine ⟨53595899900589366667643563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 285844799469809955560765669 53595899900589366667643563)
      ·
        refine ⟨80393849850884050001465345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53595899900589366667643563 80393849850884050001465345)
        ·
          refine ⟨60295387388163037501099009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80393849850884050001465345 60295387388163037501099009)
          ·
            refine ⟨45221540541122278125824257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60295387388163037501099009 45221540541122278125824257)
            ·
              refine ⟨33916155405841708594368193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45221540541122278125824257 33916155405841708594368193)
              ·
                refine ⟨25437116554381281445776145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33916155405841708594368193 25437116554381281445776145)
                ·
                  refine ⟨19077837415785961084332109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25437116554381281445776145 19077837415785961084332109)
                  ·
                    refine ⟨7154189030919735406624541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19077837415785961084332109 7154189030919735406624541)
                    ·
                      refine ⟨2682820886594900777484203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7154189030919735406624541 2682820886594900777484203)
                      ·
                        rfl

theorem cell23_5224775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 2, 3, 3].length) (baseStart_5224775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5224775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5224775 prefixEnd_5224775 := by exact prefixLift 5224775
  have htrace : WordTrace (prefixWord ++ tailWord_5224775) baseStart_5224775 baseEnd_5224775 := by
    simpa [prefixWord, tailWord_5224775, baseEnd_5224775] using wordTrace_append hprefix tailTrace_5224775
  have hstable : (prefixWord ++ tailWord_5224775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5224775).length < 2 ^ (prefixWord ++ tailWord_5224775).sum := by decide
  have hdescent : baseEnd_5224775 < baseStart_5224775 := by decide
  rcases family_descends (prefixWord ++ tailWord_5224775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5224778 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 5, 7]
def baseStart_5224778 : Nat := 118140960795 + 5224778 * 2 ^ 59
def prefixEnd_5224778 : Nat := 4983230072969 + 3 ^ 40 * 5224778 * 2
def baseEnd_5224778 : Nat := 894274142345621421915563

theorem tailTrace_5224778 : CollatzResearch.WordTrace tailWord_5224778 prefixEnd_5224778 894274142345621421915563 := by
  unfold tailWord_5224778
  simp only [CollatzResearch.WordTrace]
  refine ⟨47640827266382275471550747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127042206043686067924135325 47640827266382275471550747)
  ·
    refine ⟨71461240899573413207326121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47640827266382275471550747 71461240899573413207326121)
    ·
      refine ⟨53595930674680059905494591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71461240899573413207326121 53595930674680059905494591)
      ·
        refine ⟨80393896012020089858241887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53595930674680059905494591 80393896012020089858241887)
        ·
          refine ⟨120590844018030134787362831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80393896012020089858241887 120590844018030134787362831)
          ·
            refine ⟨180886266027045202181044247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120590844018030134787362831 180886266027045202181044247)
            ·
              refine ⟨271329399040567803271566371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180886266027045202181044247 271329399040567803271566371)
              ·
                refine ⟨406994098560851704907349557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 271329399040567803271566371 406994098560851704907349557)
                ·
                  refine ⟨38155696740079847335064021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 406994098560851704907349557 38155696740079847335064021)
                  ·
                    refine ⟨894274142345621421915563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38155696740079847335064021 894274142345621421915563)
                    ·
                      rfl

theorem cell23_5224778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 5, 7].length) (baseStart_5224778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5224778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5224778 prefixEnd_5224778 := by exact prefixLift 5224778
  have htrace : WordTrace (prefixWord ++ tailWord_5224778) baseStart_5224778 baseEnd_5224778 := by
    simpa [prefixWord, tailWord_5224778, baseEnd_5224778] using wordTrace_append hprefix tailTrace_5224778
  have hstable : (prefixWord ++ tailWord_5224778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5224778).length < 2 ^ (prefixWord ++ tailWord_5224778).sum := by decide
  have hdescent : baseEnd_5224778 < baseStart_5224778 := by decide
  rcases family_descends (prefixWord ++ tailWord_5224778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5224815 : List Nat := [1, 1, 2, 1, 3, 1, 2, 5, 2, 1, 4]
def baseStart_5224815 : Nat := 118140960795 + 5224815 * 2 ^ 59
def prefixEnd_5224815 : Nat := 4983230072969 + 3 ^ 40 * 5224815 * 2
def baseEnd_5224815 : Nat := 2682841425821080620984019

theorem tailTrace_5224815 : CollatzResearch.WordTrace tailWord_5224815 prefixEnd_5224815 2682841425821080620984019 := by
  unfold tailWord_5224815
  simp only [CollatzResearch.WordTrace]
  refine ⟨190564658566395057205299899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127043105710930038136866599 190564658566395057205299899)
  ·
    refine ⟨285846987849592585807949849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190564658566395057205299899 285846987849592585807949849)
    ·
      refine ⟨214385240887194439355962387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 285846987849592585807949849 214385240887194439355962387)
      ·
        refine ⟨321577861330791659033943581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214385240887194439355962387 321577861330791659033943581)
        ·
          refine ⟨120591697999046872137728843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 321577861330791659033943581 120591697999046872137728843)
          ·
            refine ⟨180887546998570308206593265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120591697999046872137728843 180887546998570308206593265)
            ·
              refine ⟨135665660248927731154944949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 180887546998570308206593265 135665660248927731154944949)
              ·
                refine ⟨12718655648336974795776089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 135665660248927731154944949 12718655648336974795776089)
                ·
                  refine ⟨9538991736252731096832067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12718655648336974795776089 9538991736252731096832067)
                  ·
                    refine ⟨14308487604379096645248101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9538991736252731096832067 14308487604379096645248101)
                    ·
                      refine ⟨2682841425821080620984019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14308487604379096645248101 2682841425821080620984019)
                      ·
                        rfl

theorem cell23_5224815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 5, 2, 1, 4].length) (baseStart_5224815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5224815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5224815 prefixEnd_5224815 := by exact prefixLift 5224815
  have htrace : WordTrace (prefixWord ++ tailWord_5224815) baseStart_5224815 baseEnd_5224815 := by
    simpa [prefixWord, tailWord_5224815, baseEnd_5224815] using wordTrace_append hprefix tailTrace_5224815
  have hstable : (prefixWord ++ tailWord_5224815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5224815).length < 2 ^ (prefixWord ++ tailWord_5224815).sum := by decide
  have hdescent : baseEnd_5224815 < baseStart_5224815 := by decide
  rcases family_descends (prefixWord ++ tailWord_5224815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5224825 : List Nat := [1, 2, 1, 3, 2, 1, 1, 1, 7, 4]
def baseStart_5224825 : Nat := 118140960795 + 5224825 * 2 ^ 59
def prefixEnd_5224825 : Nat := 4983230072969 + 3 ^ 40 * 5224825 * 2
def baseEnd_5224825 : Nat := 894282186875875193952991

theorem tailTrace_5224825 : CollatzResearch.WordTrace tailWord_5224825 prefixEnd_5224825 894282186875875193952991 := by
  unfold tailWord_5224825
  simp only [CollatzResearch.WordTrace]
  refine ⟨190565023296358828913163929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127043348864239219275442619 190565023296358828913163929)
  ·
    refine ⟨142923767472269121684872947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190565023296358828913163929 142923767472269121684872947)
    ·
      refine ⟨214385651208403682527309421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142923767472269121684872947 214385651208403682527309421)
      ·
        refine ⟨80394619203151380947741033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 214385651208403682527309421 80394619203151380947741033)
        ·
          refine ⟨60295964402363535710805775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80394619203151380947741033 60295964402363535710805775)
          ·
            refine ⟨90443946603545303566208663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60295964402363535710805775 90443946603545303566208663)
            ·
              refine ⟨135665919905317955349312995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90443946603545303566208663 135665919905317955349312995)
              ·
                refine ⟨203498879857976933023969493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135665919905317955349312995 203498879857976933023969493)
                ·
                  refine ⟨4769504996671334367749285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 203498879857976933023969493 4769504996671334367749285)
                  ·
                    refine ⟨894282186875875193952991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4769504996671334367749285 894282186875875193952991)
                    ·
                      rfl

theorem cell23_5224825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 7, 4].length) (baseStart_5224825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5224825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5224825 prefixEnd_5224825 := by exact prefixLift 5224825
  have htrace : WordTrace (prefixWord ++ tailWord_5224825) baseStart_5224825 baseEnd_5224825 := by
    simpa [prefixWord, tailWord_5224825, baseEnd_5224825] using wordTrace_append hprefix tailTrace_5224825
  have hstable : (prefixWord ++ tailWord_5224825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5224825).length < 2 ^ (prefixWord ++ tailWord_5224825).sum := by decide
  have hdescent : baseEnd_5224825 < baseStart_5224825 := by decide
  rcases family_descends (prefixWord ++ tailWord_5224825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5224855 : List Nat := [1, 1, 3, 3, 1, 1, 2, 5, 6]
def baseStart_5224855 : Nat := 118140960795 + 5224855 * 2 ^ 59
def prefixEnd_5224855 : Nat := 4983230072969 + 3 ^ 40 * 5224855 * 2
def baseEnd_5224855 : Nat := 298095773894140051609315

theorem tailTrace_5224855 : CollatzResearch.WordTrace tailWord_5224855 prefixEnd_5224855 298095773894140051609315 := by
  unfold tailWord_5224855
  simp only [CollatzResearch.WordTrace]
  refine ⟨190566117486250144036756019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127044078324166762691170679 190566117486250144036756019)
  ·
    refine ⟨285849176229375216055134029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190566117486250144036756019 285849176229375216055134029)
    ·
      refine ⟨107193441086015706020675261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 285849176229375216055134029 107193441086015706020675261)
      ·
        refine ⟨40197540407255889757753223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107193441086015706020675261 40197540407255889757753223)
        ·
          refine ⟨60296310610883834636629835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40197540407255889757753223 60296310610883834636629835)
          ·
            refine ⟨90444465916325751954944753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60296310610883834636629835 90444465916325751954944753)
            ·
              refine ⟨67833349437244313966208565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90444465916325751954944753 67833349437244313966208565)
              ·
                refine ⟨6359376509741654434332053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67833349437244313966208565 6359376509741654434332053)
                ·
                  refine ⟨298095773894140051609315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6359376509741654434332053 298095773894140051609315)
                  ·
                    rfl

theorem cell23_5224855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 5, 6].length) (baseStart_5224855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5224855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5224855 prefixEnd_5224855 := by exact prefixLift 5224855
  have htrace : WordTrace (prefixWord ++ tailWord_5224855) baseStart_5224855 baseEnd_5224855 := by
    simpa [prefixWord, tailWord_5224855, baseEnd_5224855] using wordTrace_append hprefix tailTrace_5224855
  have hstable : (prefixWord ++ tailWord_5224855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5224855).length < 2 ^ (prefixWord ++ tailWord_5224855).sum := by decide
  have hdescent : baseEnd_5224855 < baseStart_5224855 := by decide
  rcases family_descends (prefixWord ++ tailWord_5224855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5224872 : List Nat := [2, 1, 6, 1, 1, 1, 1, 2, 8]
def baseStart_5224872 : Nat := 118140960795 + 5224872 * 2 ^ 59
def prefixEnd_5224872 : Nat := 4983230072969 + 3 ^ 40 * 5224872 * 2
def baseEnd_5224872 : Nat := 298096743802042988663473

theorem tailTrace_5224872 : CollatzResearch.WordTrace tailWord_5224872 prefixEnd_5224872 298096743802042988663473 := by
  unfold tailWord_5224872
  simp only [CollatzResearch.WordTrace]
  refine ⟨95283368763594277970062435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127044491684792370626749913 95283368763594277970062435)
  ·
    refine ⟨142925053145391416955093653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95283368763594277970062435 142925053145391416955093653)
    ·
      refine ⟨6699611866190222669770015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 142925053145391416955093653 6699611866190222669770015)
      ·
        refine ⟨10049417799285334004655023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6699611866190222669770015 10049417799285334004655023)
        ·
          refine ⟨15074126698928001006982535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10049417799285334004655023 15074126698928001006982535)
          ·
            refine ⟨22611190048392001510473803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15074126698928001006982535 22611190048392001510473803)
            ·
              refine ⟨33916785072588002265710705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22611190048392001510473803 33916785072588002265710705)
              ·
                refine ⟨25437588804441001699283029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33916785072588002265710705 25437588804441001699283029)
                ·
                  refine ⟨298096743802042988663473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25437588804441001699283029 298096743802042988663473)
                  ·
                    rfl

theorem cell23_5224872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 8].length) (baseStart_5224872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5224872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5224872 prefixEnd_5224872 := by exact prefixLift 5224872
  have htrace : WordTrace (prefixWord ++ tailWord_5224872) baseStart_5224872 baseEnd_5224872 := by
    simpa [prefixWord, tailWord_5224872, baseEnd_5224872] using wordTrace_append hprefix tailTrace_5224872
  have hstable : (prefixWord ++ tailWord_5224872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5224872).length < 2 ^ (prefixWord ++ tailWord_5224872).sum := by decide
  have hdescent : baseEnd_5224872 < baseStart_5224872 := by decide
  rcases family_descends (prefixWord ++ tailWord_5224872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5224922 : List Nat := [3, 1, 1, 2, 3, 1, 3, 1, 3, 1, 4]
def baseStart_5224922 : Nat := 118140960795 + 5224922 * 2 ^ 59
def prefixEnd_5224922 : Nat := 4983230072969 + 3 ^ 40 * 5224922 * 2
def baseEnd_5224922 : Nat := 2682896368251111702346027

theorem tailTrace_5224922 : CollatzResearch.WordTrace tailWord_5224922 prefixEnd_5224922 2682896368251111702346027 := by
  unfold tailWord_5224922
  simp only [CollatzResearch.WordTrace]
  refine ⟨47642140294251853619861255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127045707451338276319630013 47642140294251853619861255)
  ·
    refine ⟨71463210441377780429791883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47642140294251853619861255 71463210441377780429791883)
    ·
      refine ⟨107194815662066670644687825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71463210441377780429791883 107194815662066670644687825)
      ·
        refine ⟨80396111746550002983515869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107194815662066670644687825 80396111746550002983515869)
        ·
          refine ⟨30148541904956251118818451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80396111746550002983515869 30148541904956251118818451)
          ·
            refine ⟨45222812857434376678227677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30148541904956251118818451 45222812857434376678227677)
            ·
              refine ⟨16958554821537891254335379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45222812857434376678227677 16958554821537891254335379)
              ·
                refine ⟨25437832232306836881503069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16958554821537891254335379 25437832232306836881503069)
                ·
                  refine ⟨9539187087115063830563651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25437832232306836881503069 9539187087115063830563651)
                  ·
                    refine ⟨14308780630672595745845477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9539187087115063830563651 14308780630672595745845477)
                    ·
                      refine ⟨2682896368251111702346027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14308780630672595745845477 2682896368251111702346027)
                      ·
                        rfl

theorem cell23_5224922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 3, 1, 4].length) (baseStart_5224922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5224922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5224922 prefixEnd_5224922 := by exact prefixLift 5224922
  have htrace : WordTrace (prefixWord ++ tailWord_5224922) baseStart_5224922 baseEnd_5224922 := by
    simpa [prefixWord, tailWord_5224922, baseEnd_5224922] using wordTrace_append hprefix tailTrace_5224922
  have hstable : (prefixWord ++ tailWord_5224922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5224922).length < 2 ^ (prefixWord ++ tailWord_5224922).sum := by decide
  have hdescent : baseEnd_5224922 < baseStart_5224922 := by decide
  rcases family_descends (prefixWord ++ tailWord_5224922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5224939 : List Nat := [1, 1, 1, 1, 2, 3, 7, 1, 1, 1, 4]
def baseStart_5224939 : Nat := 118140960795 + 5224939 * 2 ^ 59
def prefixEnd_5224939 : Nat := 4983230072969 + 3 ^ 40 * 5224939 * 2
def baseEnd_5224939 : Nat := 2682905097422238135833449

theorem tailTrace_5224939 : CollatzResearch.WordTrace tailWord_5224939 prefixEnd_5224939 2682905097422238135833449 := by
  unfold tailWord_5224939
  simp only [CollatzResearch.WordTrace]
  refine ⟨190569181217945826382813871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127046120811963884255209247 190569181217945826382813871)
  ·
    refine ⟨285853771826918739574220807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190569181217945826382813871 285853771826918739574220807)
    ·
      refine ⟨428780657740378109361331211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285853771826918739574220807 428780657740378109361331211)
      ·
        refine ⟨643170986610567164041996817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 428780657740378109361331211 643170986610567164041996817)
        ·
          refine ⟨482378239957925373031497613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 643170986610567164041996817 482378239957925373031497613)
          ·
            refine ⟨180891839984222014886811605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 482378239957925373031497613 180891839984222014886811605)
            ·
              refine ⟨4239652499630203473909647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 180891839984222014886811605 4239652499630203473909647)
              ·
                refine ⟨6359478749445305210864471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4239652499630203473909647 6359478749445305210864471)
                ·
                  refine ⟨9539218124167957816296707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6359478749445305210864471 9539218124167957816296707)
                  ·
                    refine ⟨14308827186251936724445061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9539218124167957816296707 14308827186251936724445061)
                    ·
                      refine ⟨2682905097422238135833449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14308827186251936724445061 2682905097422238135833449)
                      ·
                        rfl

theorem cell23_5224939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 7, 1, 1, 1, 4].length) (baseStart_5224939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5224939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5224939 prefixEnd_5224939 := by exact prefixLift 5224939
  have htrace : WordTrace (prefixWord ++ tailWord_5224939) baseStart_5224939 baseEnd_5224939 := by
    simpa [prefixWord, tailWord_5224939, baseEnd_5224939] using wordTrace_append hprefix tailTrace_5224939
  have hstable : (prefixWord ++ tailWord_5224939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5224939).length < 2 ^ (prefixWord ++ tailWord_5224939).sum := by decide
  have hdescent : baseEnd_5224939 < baseStart_5224939 := by decide
  rcases family_descends (prefixWord ++ tailWord_5224939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5224965 : List Nat := [1, 3, 1, 1, 2, 2, 2, 1, 2, 2, 6]
def baseStart_5224965 : Nat := 118140960795 + 5224965 * 2 ^ 59
def prefixEnd_5224965 : Nat := 4983230072969 + 3 ^ 40 * 5224965 * 2
def baseEnd_5224965 : Nat := 2682918447919255034108329

theorem tailTrace_5224965 : CollatzResearch.WordTrace tailWord_5224965 prefixEnd_5224965 2682918447919255034108329 := by
  unfold tailWord_5224965
  simp only [CollatzResearch.WordTrace]
  refine ⟨190570129515851632823260349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127046753010567755215506899 190570129515851632823260349)
  ·
    refine ⟨71463798568444362308722631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190570129515851632823260349 71463798568444362308722631)
    ·
      refine ⟨107195697852666543463083947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71463798568444362308722631 107195697852666543463083947)
      ·
        refine ⟨160793546778999815194625921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107195697852666543463083947 160793546778999815194625921)
        ·
          refine ⟨120595160084249861395969441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160793546778999815194625921 120595160084249861395969441)
          ·
            refine ⟨90446370063187396046977081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120595160084249861395969441 90446370063187396046977081)
            ·
              refine ⟨67834777547390547035232811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90446370063187396046977081 67834777547390547035232811)
              ·
                refine ⟨101752166321085820552849217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67834777547390547035232811 101752166321085820552849217)
                ·
                  refine ⟨76314124740814365414636913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101752166321085820552849217 76314124740814365414636913)
                  ·
                    refine ⟨57235593555610774060977685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 76314124740814365414636913 57235593555610774060977685)
                    ·
                      refine ⟨2682918447919255034108329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 57235593555610774060977685 2682918447919255034108329)
                      ·
                        rfl

theorem cell23_5224965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 2, 6].length) (baseStart_5224965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5224965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5224965 prefixEnd_5224965 := by exact prefixLift 5224965
  have htrace : WordTrace (prefixWord ++ tailWord_5224965) baseStart_5224965 baseEnd_5224965 := by
    simpa [prefixWord, tailWord_5224965, baseEnd_5224965] using wordTrace_append hprefix tailTrace_5224965
  have hstable : (prefixWord ++ tailWord_5224965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5224965).length < 2 ^ (prefixWord ++ tailWord_5224965).sum := by decide
  have hdescent : baseEnd_5224965 < baseStart_5224965 := by decide
  rcases family_descends (prefixWord ++ tailWord_5224965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5224985 : List Nat := [1, 2, 1, 2, 1, 1, 2, 3, 1, 4, 5]
def baseStart_5224985 : Nat := 118140960795 + 5224985 * 2 ^ 59
def prefixEnd_5224985 : Nat := 4983230072969 + 3 ^ 40 * 5224985 * 2
def baseEnd_5224985 : Nat := 2682928717532344955858237

theorem tailTrace_5224985 : CollatzResearch.WordTrace tailWord_5224985 prefixEnd_5224985 2682928717532344955858237 := by
  unfold tailWord_5224985
  simp only [CollatzResearch.WordTrace]
  refine ⟨190570858975779176238988409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127047239317186117492658939 190570858975779176238988409)
  ·
    refine ⟨142928144231834382179241307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190570858975779176238988409 142928144231834382179241307)
    ·
      refine ⟨214392216347751573268861961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142928144231834382179241307 214392216347751573268861961)
      ·
        refine ⟨160794162260813679951646471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214392216347751573268861961 160794162260813679951646471)
        ·
          refine ⟨241191243391220519927469707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160794162260813679951646471 241191243391220519927469707)
          ·
            refine ⟨361786865086830779891204561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241191243391220519927469707 361786865086830779891204561)
            ·
              refine ⟨271340148815123084918403421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 361786865086830779891204561 271340148815123084918403421)
              ·
                refine ⟨101752555805671156844401283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 271340148815123084918403421 101752555805671156844401283)
                ·
                  refine ⟨152628833708506735266601925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101752555805671156844401283 152628833708506735266601925)
                  ·
                    refine ⟨28617906320345012862487861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 152628833708506735266601925 28617906320345012862487861)
                    ·
                      refine ⟨2682928717532344955858237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28617906320345012862487861 2682928717532344955858237)
                      ·
                        rfl

theorem cell23_5224985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 4, 5].length) (baseStart_5224985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5224985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5224985 prefixEnd_5224985 := by exact prefixLift 5224985
  have htrace : WordTrace (prefixWord ++ tailWord_5224985) baseStart_5224985 baseEnd_5224985 := by
    simpa [prefixWord, tailWord_5224985, baseEnd_5224985] using wordTrace_append hprefix tailTrace_5224985
  have hstable : (prefixWord ++ tailWord_5224985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5224985).length < 2 ^ (prefixWord ++ tailWord_5224985).sum := by decide
  have hdescent : baseEnd_5224985 < baseStart_5224985 := by decide
  rcases family_descends (prefixWord ++ tailWord_5224985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5224989 : List Nat := [1, 4, 2, 2, 1, 2, 2, 2, 1, 3, 3]
def baseStart_5224989 : Nat := 118140960795 + 5224989 * 2 ^ 59
def prefixEnd_5224989 : Nat := 4983230072969 + 3 ^ 40 * 5224989 * 2
def baseEnd_5224989 : Nat := 2682930771454962940208219

theorem tailTrace_5224989 : CollatzResearch.WordTrace tailWord_5224989 prefixEnd_5224989 2682930771454962940208219 := by
  unfold tailWord_5224989
  simp only [CollatzResearch.WordTrace]
  refine ⟨190571004867764684922134021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127047336578509789948089347 190571004867764684922134021)
  ·
    refine ⟨35732063412705878422900129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 190571004867764684922134021 35732063412705878422900129)
    ·
      refine ⟨26799047559529408817175097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35732063412705878422900129 26799047559529408817175097)
      ·
        refine ⟨20099285669647056612881323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26799047559529408817175097 20099285669647056612881323)
        ·
          refine ⟨30148928504470584919321985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20099285669647056612881323 30148928504470584919321985)
          ·
            refine ⟨22611696378352938689491489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30148928504470584919321985 22611696378352938689491489)
            ·
              refine ⟨16958772283764704017118617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22611696378352938689491489 16958772283764704017118617)
              ·
                refine ⟨12719079212823528012838963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16958772283764704017118617 12719079212823528012838963)
                ·
                  refine ⟨19078618819235292019258445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12719079212823528012838963 19078618819235292019258445)
                  ·
                    refine ⟨7154482057213234507221917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19078618819235292019258445 7154482057213234507221917)
                    ·
                      refine ⟨2682930771454962940208219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7154482057213234507221917 2682930771454962940208219)
                      ·
                        rfl

theorem cell23_5224989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_5224989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5224989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5224989 prefixEnd_5224989 := by exact prefixLift 5224989
  have htrace : WordTrace (prefixWord ++ tailWord_5224989) baseStart_5224989 baseEnd_5224989 := by
    simpa [prefixWord, tailWord_5224989, baseEnd_5224989] using wordTrace_append hprefix tailTrace_5224989
  have hstable : (prefixWord ++ tailWord_5224989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5224989).length < 2 ^ (prefixWord ++ tailWord_5224989).sum := by decide
  have hdescent : baseEnd_5224989 < baseStart_5224989 := by decide
  rcases family_descends (prefixWord ++ tailWord_5224989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5225032 : List Nat := [2, 1, 3, 1, 1, 1, 1, 4, 2, 4, 3]
def baseStart_5225032 : Nat := 118140960795 + 5225032 * 2 ^ 59
def prefixEnd_5225032 : Nat := 4983230072969 + 3 ^ 40 * 5225032 * 2
def baseEnd_5225032 : Nat := 2682952851123106271970521

theorem tailTrace_5225032 : CollatzResearch.WordTrace tailWord_5225032 prefixEnd_5225032 2682952851123106271970521 := by
  unfold tailWord_5225032
  simp only [CollatzResearch.WordTrace]
  refine ⟨95286286603304451632974675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127048382137739268843966233 95286286603304451632974675)
  ·
    refine ⟨142929429904956677449462013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95286286603304451632974675 142929429904956677449462013)
    ·
      refine ⟨53598536214358754043548255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142929429904956677449462013 53598536214358754043548255)
      ·
        refine ⟨80397804321538131065322383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53598536214358754043548255 80397804321538131065322383)
        ·
          refine ⟨120596706482307196597983575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80397804321538131065322383 120596706482307196597983575)
          ·
            refine ⟨180895059723460794896975363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120596706482307196597983575 180895059723460794896975363)
            ·
              refine ⟨271342589585191192345463045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180895059723460794896975363 271342589585191192345463045)
              ·
                refine ⟨50876735547223348564774321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 271342589585191192345463045 50876735547223348564774321)
                ·
                  refine ⟨38157551660417511423580741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50876735547223348564774321 38157551660417511423580741)
                  ·
                    refine ⟨7154540936328283391921389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38157551660417511423580741 7154540936328283391921389)
                    ·
                      refine ⟨2682952851123106271970521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7154540936328283391921389 2682952851123106271970521)
                      ·
                        rfl

theorem cell23_5225032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 2, 4, 3].length) (baseStart_5225032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5225032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5225032 prefixEnd_5225032 := by exact prefixLift 5225032
  have htrace : WordTrace (prefixWord ++ tailWord_5225032) baseStart_5225032 baseEnd_5225032 := by
    simpa [prefixWord, tailWord_5225032, baseEnd_5225032] using wordTrace_append hprefix tailTrace_5225032
  have hstable : (prefixWord ++ tailWord_5225032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5225032).length < 2 ^ (prefixWord ++ tailWord_5225032).sum := by decide
  have hdescent : baseEnd_5225032 < baseStart_5225032 := by decide
  rcases family_descends (prefixWord ++ tailWord_5225032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5225069 : List Nat := [1, 5, 1, 1, 3, 1, 3, 1, 7]
def baseStart_5225069 : Nat := 118140960795 + 5225069 * 2 ^ 59
def prefixEnd_5225069 : Nat := 4983230072969 + 3 ^ 40 * 5225069 * 2
def baseEnd_5225069 : Nat := 298107983323035847467539

theorem tailTrace_5225069 : CollatzResearch.WordTrace tailWord_5225069 prefixEnd_5225069 298107983323035847467539 := by
  unfold tailWord_5225069
  simp only [CollatzResearch.WordTrace]
  refine ⟨190573922707474858585046261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127049281804983239056697507 190573922707474858585046261)
  ·
    refine ⟨17866305253825767992348087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 190573922707474858585046261 17866305253825767992348087)
    ·
      refine ⟨26799457880738651988522131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17866305253825767992348087 26799457880738651988522131)
      ·
        refine ⟨40199186821107977982783197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26799457880738651988522131 40199186821107977982783197)
        ·
          refine ⟨15074695057915491743543699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40199186821107977982783197 15074695057915491743543699)
          ·
            refine ⟨22612042586873237615315549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15074695057915491743543699 22612042586873237615315549)
            ·
              refine ⟨8479515970077464105743331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22612042586873237615315549 8479515970077464105743331)
              ·
                refine ⟨12719273955116196158614997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8479515970077464105743331 12719273955116196158614997)
                ·
                  refine ⟨298107983323035847467539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12719273955116196158614997 298107983323035847467539)
                  ·
                    rfl

theorem cell23_5225069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 1, 7].length) (baseStart_5225069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5225069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5225069 prefixEnd_5225069 := by exact prefixLift 5225069
  have htrace : WordTrace (prefixWord ++ tailWord_5225069) baseStart_5225069 baseEnd_5225069 := by
    simpa [prefixWord, tailWord_5225069, baseEnd_5225069] using wordTrace_append hprefix tailTrace_5225069
  have hstable : (prefixWord ++ tailWord_5225069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5225069).length < 2 ^ (prefixWord ++ tailWord_5225069).sum := by decide
  have hdescent : baseEnd_5225069 < baseStart_5225069 := by decide
  rcases family_descends (prefixWord ++ tailWord_5225069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5225120 : List Nat := [2, 1, 1, 4, 5, 1, 2, 2, 5]
def baseStart_5225120 : Nat := 118140960795 + 5225120 * 2 ^ 59
def prefixEnd_5225120 : Nat := 4983230072969 + 3 ^ 40 * 5225120 * 2
def baseEnd_5225120 : Nat := 298110893046744658630013

theorem tailTrace_5225120 : CollatzResearch.WordTrace tailWord_5225120 prefixEnd_5225120 298110893046744658630013 := by
  unfold tailWord_5225120
  simp only [CollatzResearch.WordTrace]
  refine ⟨95287891415145047147576407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127050521886860062863435209 95287891415145047147576407)
  ·
    refine ⟨142931837122717570721364611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95287891415145047147576407 142931837122717570721364611)
    ·
      refine ⟨214397755684076356082046917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142931837122717570721364611 214397755684076356082046917)
      ·
        refine ⟨40199579190764316765383797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 214397755684076356082046917 40199579190764316765383797)
        ·
          refine ⟨3768710549134154696754731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40199579190764316765383797 3768710549134154696754731)
          ·
            refine ⟨5653065823701232045132097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3768710549134154696754731 5653065823701232045132097)
            ·
              refine ⟨4239799367775924033849073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5653065823701232045132097 4239799367775924033849073)
              ·
                refine ⟨3179849525831943025386805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4239799367775924033849073 3179849525831943025386805)
                ·
                  refine ⟨298110893046744658630013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3179849525831943025386805 298110893046744658630013)
                  ·
                    rfl

theorem cell23_5225120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 2, 2, 5].length) (baseStart_5225120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5225120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5225120 prefixEnd_5225120 := by exact prefixLift 5225120
  have htrace : WordTrace (prefixWord ++ tailWord_5225120) baseStart_5225120 baseEnd_5225120 := by
    simpa [prefixWord, tailWord_5225120, baseEnd_5225120] using wordTrace_append hprefix tailTrace_5225120
  have hstable : (prefixWord ++ tailWord_5225120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5225120).length < 2 ^ (prefixWord ++ tailWord_5225120).sum := by decide
  have hdescent : baseEnd_5225120 < baseStart_5225120 := by decide
  rcases family_descends (prefixWord ++ tailWord_5225120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5225153 : List Nat := [1, 2, 6, 2, 1, 1, 1, 1, 1, 3, 4]
def baseStart_5225153 : Nat := 118140960795 + 5225153 * 2 ^ 59
def prefixEnd_5225153 : Nat := 4983230072969 + 3 ^ 40 * 5225153 * 2
def baseEnd_5225153 : Nat := 2683014982282300298557465

theorem tailTrace_5225153 : CollatzResearch.WordTrace tailWord_5225153 prefixEnd_5225153 2683014982282300298557465 := by
  unfold tailWord_5225153
  simp only [CollatzResearch.WordTrace]
  refine ⟨190576986439170540931104113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127051324292780360620736075 190576986439170540931104113)
  ·
    refine ⟨142932739829377905698328085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190576986439170540931104113 142932739829377905698328085)
    ·
      refine ⟨6699972179502089329609129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 142932739829377905698328085 6699972179502089329609129)
      ·
        refine ⟨5024979134626566997206847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6699972179502089329609129 5024979134626566997206847)
        ·
          refine ⟨7537468701939850495810271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5024979134626566997206847 7537468701939850495810271)
          ·
            refine ⟨11306203052909775743715407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7537468701939850495810271 11306203052909775743715407)
            ·
              refine ⟨16959304579364663615573111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11306203052909775743715407 16959304579364663615573111)
              ·
                refine ⟨25438956869046995423359667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16959304579364663615573111 25438956869046995423359667)
                ·
                  refine ⟨38158435303570493135039501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25438956869046995423359667 38158435303570493135039501)
                  ·
                    refine ⟨14309413238838934925639813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38158435303570493135039501 14309413238838934925639813)
                    ·
                      refine ⟨2683014982282300298557465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14309413238838934925639813 2683014982282300298557465)
                      ·
                        rfl

theorem cell23_5225153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_5225153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5225153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5225153 prefixEnd_5225153 := by exact prefixLift 5225153
  have htrace : WordTrace (prefixWord ++ tailWord_5225153) baseStart_5225153 baseEnd_5225153 := by
    simpa [prefixWord, tailWord_5225153, baseEnd_5225153] using wordTrace_append hprefix tailTrace_5225153
  have hstable : (prefixWord ++ tailWord_5225153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5225153).length < 2 ^ (prefixWord ++ tailWord_5225153).sum := by decide
  have hdescent : baseEnd_5225153 < baseStart_5225153 := by decide
  rcases family_descends (prefixWord ++ tailWord_5225153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5225156 : List Nat := [2, 3, 3, 1, 1, 3, 1, 1, 1, 4, 3]
def baseStart_5225156 : Nat := 118140960795 + 5225156 * 2 ^ 59
def prefixEnd_5225156 : Nat := 4983230072969 + 3 ^ 40 * 5225156 * 2
def baseEnd_5225156 : Nat := 2683016522724263786819951

theorem tailTrace_5225156 : CollatzResearch.WordTrace tailWord_5225156 prefixEnd_5225156 2683016522724263786819951 := by
  unfold tailWord_5225156
  simp only [CollatzResearch.WordTrace]
  refine ⟨95288547929079836221731661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127051397238773114962308881 95288547929079836221731661)
  ·
    refine ⟨35733205473404938583149373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95288547929079836221731661 35733205473404938583149373)
    ·
      refine ⟨13399952052526851968681015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35733205473404938583149373 13399952052526851968681015)
      ·
        refine ⟨20099928078790277953021523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13399952052526851968681015 20099928078790277953021523)
        ·
          refine ⟨30149892118185416929532285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20099928078790277953021523 30149892118185416929532285)
          ·
            refine ⟨11306209544319531348574607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30149892118185416929532285 11306209544319531348574607)
            ·
              refine ⟨16959314316479297022861911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11306209544319531348574607 16959314316479297022861911)
              ·
                refine ⟨25438971474718945534292867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16959314316479297022861911 25438971474718945534292867)
                ·
                  refine ⟨38158457212078418301439301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25438971474718945534292867 38158457212078418301439301)
                  ·
                    refine ⟨7154710727264703431519869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38158457212078418301439301 7154710727264703431519869)
                    ·
                      refine ⟨2683016522724263786819951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7154710727264703431519869 2683016522724263786819951)
                      ·
                        rfl

theorem cell23_5225156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_5225156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5225156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5225156 prefixEnd_5225156 := by exact prefixLift 5225156
  have htrace : WordTrace (prefixWord ++ tailWord_5225156) baseStart_5225156 baseEnd_5225156 := by
    simpa [prefixWord, tailWord_5225156, baseEnd_5225156] using wordTrace_append hprefix tailTrace_5225156
  have hstable : (prefixWord ++ tailWord_5225156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5225156).length < 2 ^ (prefixWord ++ tailWord_5225156).sum := by decide
  have hdescent : baseEnd_5225156 < baseStart_5225156 := by decide
  rcases family_descends (prefixWord ++ tailWord_5225156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5225176 : List Nat := [2, 1, 2, 2, 3, 4, 1, 2, 6]
def baseStart_5225176 : Nat := 118140960795 + 5225176 * 2 ^ 59
def prefixEnd_5225176 : Nat := 4983230072969 + 3 ^ 40 * 5225176 * 2
def baseEnd_5225176 : Nat := 298114088037483745396651

theorem tailTrace_5225176 : CollatzResearch.WordTrace tailWord_5225176 prefixEnd_5225176 298114088037483745396651 := by
  unfold tailWord_5225176
  simp only [CollatzResearch.WordTrace]
  refine ⟨95288912659043607929595691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127051883545391477239460921 95288912659043607929595691)
  ·
    refine ⟨142933368988565411894393537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95288912659043607929595691 142933368988565411894393537)
    ·
      refine ⟨107200026741424058920795153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142933368988565411894393537 107200026741424058920795153)
      ·
        refine ⟨80400020056068044190596365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107200026741424058920795153 80400020056068044190596365)
        ·
          refine ⟨30150007521025516571473637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80400020056068044190596365 30150007521025516571473637)
          ·
            refine ⟨5653126410192284357151307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30150007521025516571473637 5653126410192284357151307)
            ·
              refine ⟨8479689615288426535726961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5653126410192284357151307 8479689615288426535726961)
              ·
                refine ⟨6359767211466319901795221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8479689615288426535726961 6359767211466319901795221)
                ·
                  refine ⟨298114088037483745396651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6359767211466319901795221 298114088037483745396651)
                  ·
                    rfl

theorem cell23_5225176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 2, 6].length) (baseStart_5225176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5225176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5225176 prefixEnd_5225176 := by exact prefixLift 5225176
  have htrace : WordTrace (prefixWord ++ tailWord_5225176) baseStart_5225176 baseEnd_5225176 := by
    simpa [prefixWord, tailWord_5225176, baseEnd_5225176] using wordTrace_append hprefix tailTrace_5225176
  have hstable : (prefixWord ++ tailWord_5225176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5225176).length < 2 ^ (prefixWord ++ tailWord_5225176).sum := by decide
  have hdescent : baseEnd_5225176 < baseStart_5225176 := by decide
  rcases family_descends (prefixWord ++ tailWord_5225176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5225179 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 2, 9, 2]
def baseStart_5225179 : Nat := 118140960795 + 5225179 * 2 ^ 59
def prefixEnd_5225179 : Nat := 4983230072969 + 3 ^ 40 * 5225179 * 2
def baseEnd_5225179 : Nat := 2683028332779317196832345

theorem tailTrace_5225179 : CollatzResearch.WordTrace tailWord_5225179 prefixEnd_5225179 2683028332779317196832345 := by
  unfold tailWord_5225179
  simp only [CollatzResearch.WordTrace]
  refine ⟨190577934737076347371550591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127051956491384231581033727 190577934737076347371550591)
  ·
    refine ⟨285866902105614521057325887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190577934737076347371550591 285866902105614521057325887)
    ·
      refine ⟨428800353158421781585988831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285866902105614521057325887 428800353158421781585988831)
      ·
        refine ⟨643200529737632672378983247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 428800353158421781585988831 643200529737632672378983247)
        ·
          refine ⟨964800794606449008568474871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 643200529737632672378983247 964800794606449008568474871)
          ·
            refine ⟨1447201191909673512852712307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 964800794606449008568474871 1447201191909673512852712307)
            ·
              refine ⟨2170801787864510269279068461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1447201191909673512852712307 2170801787864510269279068461)
              ·
                refine ⟨814050670449191350979650673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2170801787864510269279068461 814050670449191350979650673)
                ·
                  refine ⟨610538002836893513234738005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 814050670449191350979650673 610538002836893513234738005)
                  ·
                    refine ⟨3577371110372422929109793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 610538002836893513234738005 3577371110372422929109793)
                    ·
                      refine ⟨2683028332779317196832345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3577371110372422929109793 2683028332779317196832345)
                      ·
                        rfl

theorem cell23_5225179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 9, 2].length) (baseStart_5225179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5225179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5225179 prefixEnd_5225179 := by exact prefixLift 5225179
  have htrace : WordTrace (prefixWord ++ tailWord_5225179) baseStart_5225179 baseEnd_5225179 := by
    simpa [prefixWord, tailWord_5225179, baseEnd_5225179] using wordTrace_append hprefix tailTrace_5225179
  have hstable : (prefixWord ++ tailWord_5225179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5225179).length < 2 ^ (prefixWord ++ tailWord_5225179).sum := by decide
  have hdescent : baseEnd_5225179 < baseStart_5225179 := by decide
  rcases family_descends (prefixWord ++ tailWord_5225179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5225180 : List Nat := [2, 2, 5, 1, 1, 1, 2, 4, 1, 4]
def baseStart_5225180 : Nat := 118140960795 + 5225180 * 2 ^ 59
def prefixEnd_5225180 : Nat := 4983230072969 + 3 ^ 40 * 5225180 * 2
def baseEnd_5225180 : Nat := 894342948753323897639947

theorem tailTrace_5225180 : CollatzResearch.WordTrace tailWord_5225180 prefixEnd_5225180 894342948753323897639947 := by
  unfold tailWord_5225180
  simp only [CollatzResearch.WordTrace]
  refine ⟨95288985605036362271168497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127051980806715149694891329 95288985605036362271168497)
  ·
    refine ⟨71466739203777271703376373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95288985605036362271168497 71466739203777271703376373)
    ·
      refine ⟨6700006800354119222191535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 71466739203777271703376373 6700006800354119222191535)
      ·
        refine ⟨10050010200531178833287303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6700006800354119222191535 10050010200531178833287303)
        ·
          refine ⟨15075015300796768249930955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10050010200531178833287303 15075015300796768249930955)
          ·
            refine ⟨22612522951195152374896433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15075015300796768249930955 22612522951195152374896433)
            ·
              refine ⟨16959392213396364281172325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22612522951195152374896433 16959392213396364281172325)
              ·
                refine ⟨3179886040011818302719811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16959392213396364281172325 3179886040011818302719811)
                ·
                  refine ⟨4769829060017727454079717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3179886040011818302719811 4769829060017727454079717)
                  ·
                    refine ⟨894342948753323897639947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4769829060017727454079717 894342948753323897639947)
                    ·
                      rfl

theorem cell23_5225180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_5225180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5225180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5225180 prefixEnd_5225180 := by exact prefixLift 5225180
  have htrace : WordTrace (prefixWord ++ tailWord_5225180) baseStart_5225180 baseEnd_5225180 := by
    simpa [prefixWord, tailWord_5225180, baseEnd_5225180] using wordTrace_append hprefix tailTrace_5225180
  have hstable : (prefixWord ++ tailWord_5225180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5225180).length < 2 ^ (prefixWord ++ tailWord_5225180).sum := by decide
  have hdescent : baseEnd_5225180 < baseStart_5225180 := by decide
  rcases family_descends (prefixWord ++ tailWord_5225180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5225209 : List Nat := [1, 2, 1, 3, 1, 1, 1, 5, 3, 1, 4]
def baseStart_5225209 : Nat := 118140960795 + 5225209 * 2 ^ 59
def prefixEnd_5225209 : Nat := 4983230072969 + 3 ^ 40 * 5225209 * 2
def baseEnd_5225209 : Nat := 2683043737198952079457207

theorem tailTrace_5225209 : CollatzResearch.WordTrace tailWord_5225209 prefixEnd_5225209 2683043737198952079457207 := by
  unfold tailWord_5225209
  simp only [CollatzResearch.WordTrace]
  refine ⟨190579028926967662495142681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127052685951311774996761787 190579028926967662495142681)
  ·
    refine ⟨142934271695225746871357011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190579028926967662495142681 142934271695225746871357011)
    ·
      refine ⟨214401407542838620307035517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142934271695225746871357011 214401407542838620307035517)
      ·
        refine ⟨80400527828564482615138319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 214401407542838620307035517 80400527828564482615138319)
        ·
          refine ⟨120600791742846723922707479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80400527828564482615138319 120600791742846723922707479)
          ·
            refine ⟨180901187614270085884061219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120600791742846723922707479 180901187614270085884061219)
            ·
              refine ⟨271351781421405128826091829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180901187614270085884061219 271351781421405128826091829)
              ·
                refine ⟨25439229508256730827446109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 271351781421405128826091829 25439229508256730827446109)
                ·
                  refine ⟨9539711065596274060292291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25439229508256730827446109 9539711065596274060292291)
                  ·
                    refine ⟨14309566598394411090438437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9539711065596274060292291 14309566598394411090438437)
                    ·
                      refine ⟨2683043737198952079457207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14309566598394411090438437 2683043737198952079457207)
                      ·
                        rfl

theorem cell23_5225209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 3, 1, 4].length) (baseStart_5225209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5225209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5225209 prefixEnd_5225209 := by exact prefixLift 5225209
  have htrace : WordTrace (prefixWord ++ tailWord_5225209) baseStart_5225209 baseEnd_5225209 := by
    simpa [prefixWord, tailWord_5225209, baseEnd_5225209] using wordTrace_append hprefix tailTrace_5225209
  have hstable : (prefixWord ++ tailWord_5225209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5225209).length < 2 ^ (prefixWord ++ tailWord_5225209).sum := by decide
  have hdescent : baseEnd_5225209 < baseStart_5225209 := by decide
  rcases family_descends (prefixWord ++ tailWord_5225209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5225226 : List Nat := [3, 1, 2, 2, 1, 2, 1, 5, 1, 1, 4]
def baseStart_5225226 : Nat := 118140960795 + 5225226 * 2 ^ 59
def prefixEnd_5225226 : Nat := 4983230072969 + 3 ^ 40 * 5225226 * 2
def baseEnd_5225226 : Nat := 2683052466370078512944629

theorem tailTrace_5225226 : CollatzResearch.WordTrace tailWord_5225226 prefixEnd_5225226 2683052466370078512944629 := by
  unfold tailWord_5225226
  simp only [CollatzResearch.WordTrace]
  refine ⟨47644912241976518599627883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127053099311937382932341021 47644912241976518599627883)
  ·
    refine ⟨71467368362964777899441825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47644912241976518599627883 71467368362964777899441825)
    ·
      refine ⟨53600526272223583424581369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71467368362964777899441825 53600526272223583424581369)
      ·
        refine ⟨40200394704167687568436027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53600526272223583424581369 40200394704167687568436027)
        ·
          refine ⟨60300592056251531352654041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40200394704167687568436027 60300592056251531352654041)
          ·
            refine ⟨45225444042188648514490531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60300592056251531352654041 45225444042188648514490531)
            ·
              refine ⟨67838166063282972771735797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45225444042188648514490531 67838166063282972771735797)
              ·
                refine ⟨6359828068432778697350231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67838166063282972771735797 6359828068432778697350231)
                ·
                  refine ⟨9539742102649168046025347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6359828068432778697350231 9539742102649168046025347)
                  ·
                    refine ⟨14309613153973752069038021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9539742102649168046025347 14309613153973752069038021)
                    ·
                      refine ⟨2683052466370078512944629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14309613153973752069038021 2683052466370078512944629)
                      ·
                        rfl

theorem cell23_5225226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 5, 1, 1, 4].length) (baseStart_5225226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5225226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5225226 prefixEnd_5225226 := by exact prefixLift 5225226
  have htrace : WordTrace (prefixWord ++ tailWord_5225226) baseStart_5225226 baseEnd_5225226 := by
    simpa [prefixWord, tailWord_5225226, baseEnd_5225226] using wordTrace_append hprefix tailTrace_5225226
  have hstable : (prefixWord ++ tailWord_5225226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5225226).length < 2 ^ (prefixWord ++ tailWord_5225226).sum := by decide
  have hdescent : baseEnd_5225226 < baseStart_5225226 := by decide
  rcases family_descends (prefixWord ++ tailWord_5225226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5225249 : List Nat := [1, 2, 3, 2, 1, 2, 4, 8]
def baseStart_5225249 : Nat := 118140960795 + 5225249 * 2 ^ 59
def prefixEnd_5225249 : Nat := 4983230072969 + 3 ^ 40 * 5225249 * 2
def baseEnd_5225249 : Nat := 99372750978708589739149

theorem tailTrace_5225249 : CollatzResearch.WordTrace tailWord_5225249 prefixEnd_5225249 99372750978708589739149 := by
  unfold tailWord_5225249
  simp only [CollatzResearch.WordTrace]
  refine ⟨190580487846822749326598801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127053658564548499551065867 190580487846822749326598801)
  ·
    refine ⟨142935365885117061994949101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190580487846822749326598801 142935365885117061994949101)
    ·
      refine ⟨53600762206918898248105913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142935365885117061994949101 53600762206918898248105913)
      ·
        refine ⟨40200571655189173686079435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53600762206918898248105913 40200571655189173686079435)
        ·
          refine ⟨60300857482783760529119153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40200571655189173686079435 60300857482783760529119153)
          ·
            refine ⟨45225643112087820396839365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60300857482783760529119153 45225643112087820396839365)
            ·
              refine ⟨8479808083516466324407381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45225643112087820396839365 8479808083516466324407381)
              ·
                refine ⟨99372750978708589739149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8479808083516466324407381 99372750978708589739149)
                ·
                  rfl

theorem cell23_5225249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 8].length) (baseStart_5225249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5225249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5225249 prefixEnd_5225249 := by exact prefixLift 5225249
  have htrace : WordTrace (prefixWord ++ tailWord_5225249) baseStart_5225249 baseEnd_5225249 := by
    simpa [prefixWord, tailWord_5225249, baseEnd_5225249] using wordTrace_append hprefix tailTrace_5225249
  have hstable : (prefixWord ++ tailWord_5225249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5225249).length < 2 ^ (prefixWord ++ tailWord_5225249).sum := by decide
  have hdescent : baseEnd_5225249 < baseStart_5225249 := by decide
  rcases family_descends (prefixWord ++ tailWord_5225249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5225256 : List Nat := [2, 1, 5, 1, 1, 1, 2, 3, 1, 2, 4]
def baseStart_5225256 : Nat := 118140960795 + 5225256 * 2 ^ 59
def prefixEnd_5225256 : Nat := 4983230072969 + 3 ^ 40 * 5225256 * 2
def baseEnd_5225256 : Nat := 2683067870789713395569491

theorem tailTrace_5225256 : CollatzResearch.WordTrace tailWord_5225256 prefixEnd_5225256 2683067870789713395569491 := by
  unfold tailWord_5225256
  simp only [CollatzResearch.WordTrace]
  refine ⟨95290371578898694761051811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 127053828771864926348069081 95290371578898694761051811)
  ·
    refine ⟨142935557368348042141577717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95290371578898694761051811 142935557368348042141577717)
    ·
      refine ⟨13400208503282628950772911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 142935557368348042141577717 13400208503282628950772911)
      ·
        refine ⟨20100312754923943426159367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13400208503282628950772911 20100312754923943426159367)
        ·
          refine ⟨30150469132385915139239051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20100312754923943426159367 30150469132385915139239051)
          ·
            refine ⟨45225703698578872708858577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30150469132385915139239051 45225703698578872708858577)
            ·
              refine ⟨33919277773934154531643933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45225703698578872708858577 33919277773934154531643933)
              ·
                refine ⟨12719729165225307949366475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33919277773934154531643933 12719729165225307949366475)
                ·
                  refine ⟨19079593747837961924049713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12719729165225307949366475 19079593747837961924049713)
                  ·
                    refine ⟨14309695310878471443037285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19079593747837961924049713 14309695310878471443037285)
                    ·
                      refine ⟨2683067870789713395569491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14309695310878471443037285 2683067870789713395569491)
                      ·
                        rfl

theorem cell23_5225256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_5225256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5225256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5225256 prefixEnd_5225256 := by exact prefixLift 5225256
  have htrace : WordTrace (prefixWord ++ tailWord_5225256) baseStart_5225256 baseEnd_5225256 := by
    simpa [prefixWord, tailWord_5225256, baseEnd_5225256] using wordTrace_append hprefix tailTrace_5225256
  have hstable : (prefixWord ++ tailWord_5225256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5225256).length < 2 ^ (prefixWord ++ tailWord_5225256).sum := by decide
  have hdescent : baseEnd_5225256 < baseStart_5225256 := by decide
  rcases family_descends (prefixWord ++ tailWord_5225256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5225303 : List Nat := [1, 1, 3, 2, 4, 1, 1, 2, 3, 3, 2]
def baseStart_5225303 : Nat := 118140960795 + 5225303 * 2 ^ 59
def prefixEnd_5225303 : Nat := 4983230072969 + 3 ^ 40 * 5225303 * 2
def baseEnd_5225303 : Nat := 2683092004380474711681775

theorem tailTrace_5225303 : CollatzResearch.WordTrace tailWord_5225303 prefixEnd_5225303 2683092004380474711681775 := by
  unfold tailWord_5225303
  simp only [CollatzResearch.WordTrace]
  refine ⟨190582457388627116549064563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127054971592418077699376375 190582457388627116549064563)
  ·
    refine ⟨285873686082940674823596845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190582457388627116549064563 285873686082940674823596845)
    ·
      refine ⟨107202632281102753058848817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 285873686082940674823596845 107202632281102753058848817)
      ·
        refine ⟨80401974210827064794136613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107202632281102753058848817 80401974210827064794136613)
        ·
          refine ⟨15075370164530074648900615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80401974210827064794136613 15075370164530074648900615)
          ·
            refine ⟨22613055246795111973350923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15075370164530074648900615 22613055246795111973350923)
            ·
              refine ⟨33919582870192667960026385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22613055246795111973350923 33919582870192667960026385)
              ·
                refine ⟨25439687152644500970019789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33919582870192667960026385 25439687152644500970019789)
                ·
                  refine ⟨9539882682241687863757421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25439687152644500970019789 9539882682241687863757421)
                  ·
                    refine ⟨3577456005840632948909033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9539882682241687863757421 3577456005840632948909033)
                    ·
                      refine ⟨2683092004380474711681775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3577456005840632948909033 2683092004380474711681775)
                      ·
                        rfl

theorem cell23_5225303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 3, 3, 2].length) (baseStart_5225303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5225303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5225303 prefixEnd_5225303 := by exact prefixLift 5225303
  have htrace : WordTrace (prefixWord ++ tailWord_5225303) baseStart_5225303 baseEnd_5225303 := by
    simpa [prefixWord, tailWord_5225303, baseEnd_5225303] using wordTrace_append hprefix tailTrace_5225303
  have hstable : (prefixWord ++ tailWord_5225303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5225303).length < 2 ^ (prefixWord ++ tailWord_5225303).sum := by decide
  have hdescent : baseEnd_5225303 < baseStart_5225303 := by decide
  rcases family_descends (prefixWord ++ tailWord_5225303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5225337 : List Nat := [1, 2, 1, 3, 2, 5, 2, 1, 1, 3, 2]
def baseStart_5225337 : Nat := 118140960795 + 5225337 * 2 ^ 59
def prefixEnd_5225337 : Nat := 4983230072969 + 3 ^ 40 * 5225337 * 2
def baseEnd_5225337 : Nat := 2683109462722727578656619

theorem tailTrace_5225337 : CollatzResearch.WordTrace tailWord_5225337 prefixEnd_5225337 2683109462722727578656619 := by
  unfold tailWord_5225337
  simp only [CollatzResearch.WordTrace]
  refine ⟨190583697470503940355802265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127055798313669293570534843 190583697470503940355802265)
  ·
    refine ⟨142937773102877955266851699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 190583697470503940355802265 142937773102877955266851699)
    ·
      refine ⟨214406659654316932900277549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142937773102877955266851699 214406659654316932900277549)
      ·
        refine ⟨80402497370368849837604081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 214406659654316932900277549 80402497370368849837604081)
        ·
          refine ⟨60301873027776637378203061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80402497370368849837604081 60301873027776637378203061)
          ·
            refine ⟨5653300596354059754206537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60301873027776637378203061 5653300596354059754206537)
            ·
              refine ⟨4239975447265544815654903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5653300596354059754206537 4239975447265544815654903)
              ·
                refine ⟨6359963170898317223482355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4239975447265544815654903 6359963170898317223482355)
                ·
                  refine ⟨9539944756347475835223533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6359963170898317223482355 9539944756347475835223533)
                  ·
                    refine ⟨3577479283630303438208825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9539944756347475835223533 3577479283630303438208825)
                    ·
                      refine ⟨2683109462722727578656619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3577479283630303438208825 2683109462722727578656619)
                      ·
                        rfl

theorem cell23_5225337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 2, 1, 1, 3, 2].length) (baseStart_5225337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5225337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5225337 prefixEnd_5225337 := by exact prefixLift 5225337
  have htrace : WordTrace (prefixWord ++ tailWord_5225337) baseStart_5225337 baseEnd_5225337 := by
    simpa [prefixWord, tailWord_5225337, baseEnd_5225337] using wordTrace_append hprefix tailTrace_5225337
  have hstable : (prefixWord ++ tailWord_5225337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5225337).length < 2 ^ (prefixWord ++ tailWord_5225337).sum := by decide
  have hdescent : baseEnd_5225337 < baseStart_5225337 := by decide
  rcases family_descends (prefixWord ++ tailWord_5225337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5225367 : List Nat := [1, 1, 3, 3, 1, 2, 5, 1, 2, 2, 2]
def baseStart_5225367 : Nat := 118140960795 + 5225367 * 2 ^ 59
def prefixEnd_5225367 : Nat := 4983230072969 + 3 ^ 40 * 5225367 * 2
def baseEnd_5225367 : Nat := 2683124867142362461281481

theorem tailTrace_5225367 : CollatzResearch.WordTrace tailWord_5225367 prefixEnd_5225367 2683124867142362461281481 := by
  unfold tailWord_5225367
  simp only [CollatzResearch.WordTrace]
  refine ⟨190584791660395255479394355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127056527773596836986262903 190584791660395255479394355)
  ·
    refine ⟨285877187490592883219091533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190584791660395255479394355 285877187490592883219091533)
    ·
      refine ⟨107203945308972331207159325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 285877187490592883219091533 107203945308972331207159325)
      ·
        refine ⟨40201479490864624202684747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107203945308972331207159325 40201479490864624202684747)
        ·
          refine ⟨60302219236296936304027121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40201479490864624202684747 60302219236296936304027121)
          ·
            refine ⟨45226664427222702228020341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60302219236296936304027121 45226664427222702228020341)
            ·
              refine ⟨4239999790052128333876907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45226664427222702228020341 4239999790052128333876907)
              ·
                refine ⟨6359999685078192500815361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4239999790052128333876907 6359999685078192500815361)
                ·
                  refine ⟨4769999763808644375611521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6359999685078192500815361 4769999763808644375611521)
                  ·
                    refine ⟨3577499822856483281708641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4769999763808644375611521 3577499822856483281708641)
                    ·
                      refine ⟨2683124867142362461281481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3577499822856483281708641 2683124867142362461281481)
                      ·
                        rfl

theorem cell23_5225367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 5, 1, 2, 2, 2].length) (baseStart_5225367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5225367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5225367 prefixEnd_5225367 := by exact prefixLift 5225367
  have htrace : WordTrace (prefixWord ++ tailWord_5225367) baseStart_5225367 baseEnd_5225367 := by
    simpa [prefixWord, tailWord_5225367, baseEnd_5225367] using wordTrace_append hprefix tailTrace_5225367
  have hstable : (prefixWord ++ tailWord_5225367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5225367).length < 2 ^ (prefixWord ++ tailWord_5225367).sum := by decide
  have hdescent : baseEnd_5225367 < baseStart_5225367 := by decide
  rcases family_descends (prefixWord ++ tailWord_5225367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5225474 : List Nat := [3, 4, 1, 3, 1, 1, 1, 1, 2, 4, 2]
def baseStart_5225474 : Nat := 118140960795 + 5225474 * 2 ^ 59
def prefixEnd_5225474 : Nat := 4983230072969 + 3 ^ 40 * 5225474 * 2
def baseEnd_5225474 : Nat := 2683179809572393542643489

theorem tailTrace_5225474 : CollatzResearch.WordTrace tailWord_5225474 prefixEnd_5225474 2683179809572393542643489 := by
  unfold tailWord_5225474
  simp only [CollatzResearch.WordTrace]
  refine ⟨47647173567751903188384869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 127059129514005075169026317 47647173567751903188384869)
  ·
    refine ⟨8933845043953481847822163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47647173567751903188384869 8933845043953481847822163)
    ·
      refine ⟨13400767565930222771733245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8933845043953481847822163 13400767565930222771733245)
      ·
        refine ⟨5025287837223833539399967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13400767565930222771733245 5025287837223833539399967)
        ·
          refine ⟨7537931755835750309099951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5025287837223833539399967 7537931755835750309099951)
          ·
            refine ⟨11306897633753625463649927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7537931755835750309099951 11306897633753625463649927)
            ·
              refine ⟨16960346450630438195474891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11306897633753625463649927 16960346450630438195474891)
              ·
                refine ⟨25440519675945657293212337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16960346450630438195474891 25440519675945657293212337)
                ·
                  refine ⟨19080389756959242969909253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25440519675945657293212337 19080389756959242969909253)
                  ·
                    refine ⟨3577573079429858056857985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19080389756959242969909253 3577573079429858056857985)
                    ·
                      refine ⟨2683179809572393542643489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3577573079429858056857985 2683179809572393542643489)
                      ·
                        rfl

theorem cell23_5225474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_5225474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5225474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5225474 prefixEnd_5225474 := by exact prefixLift 5225474
  have htrace : WordTrace (prefixWord ++ tailWord_5225474) baseStart_5225474 baseEnd_5225474 := by
    simpa [prefixWord, tailWord_5225474, baseEnd_5225474] using wordTrace_append hprefix tailTrace_5225474
  have hstable : (prefixWord ++ tailWord_5225474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5225474).length < 2 ^ (prefixWord ++ tailWord_5225474).sum := by decide
  have hdescent : baseEnd_5225474 < baseStart_5225474 := by decide
  rcases family_descends (prefixWord ++ tailWord_5225474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5225493 : List Nat := [1, 3, 2, 1, 4, 1, 2, 1, 3, 5]
def baseStart_5225493 : Nat := 118140960795 + 5225493 * 2 ^ 59
def prefixEnd_5225493 : Nat := 4983230072969 + 3 ^ 40 * 5225493 * 2
def baseEnd_5225493 : Nat := 894396521901609656101967

theorem tailTrace_5225493 : CollatzResearch.WordTrace tailWord_5225493 prefixEnd_5225493 894396521901609656101967 := by
  unfold tailWord_5225493
  simp only [CollatzResearch.WordTrace]
  refine ⟨190589387257938778998481133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127059591505292519332320755 190589387257938778998481133)
  ·
    refine ⟨71471020221727042124430425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 190589387257938778998481133 71471020221727042124430425)
    ·
      refine ⟨53603265166295281593322819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71471020221727042124430425 53603265166295281593322819)
      ·
        refine ⟨80404897749442922389984229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53603265166295281593322819 80404897749442922389984229)
        ·
          refine ⟨15075918328020547948122043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80404897749442922389984229 15075918328020547948122043)
          ·
            refine ⟨22613877492030821922183065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15075918328020547948122043 22613877492030821922183065)
            ·
              refine ⟨16960408119023116441637299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22613877492030821922183065 16960408119023116441637299)
              ·
                refine ⟨25440612178534674662455949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16960408119023116441637299 25440612178534674662455949)
                ·
                  refine ⟨9540229566950502998420981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25440612178534674662455949 9540229566950502998420981)
                  ·
                    refine ⟨894396521901609656101967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9540229566950502998420981 894396521901609656101967)
                    ·
                      rfl

theorem cell23_5225493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 3, 5].length) (baseStart_5225493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5225493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5225493 prefixEnd_5225493 := by exact prefixLift 5225493
  have htrace : WordTrace (prefixWord ++ tailWord_5225493) baseStart_5225493 baseEnd_5225493 := by
    simpa [prefixWord, tailWord_5225493, baseEnd_5225493] using wordTrace_append hprefix tailTrace_5225493
  have hstable : (prefixWord ++ tailWord_5225493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5225493).length < 2 ^ (prefixWord ++ tailWord_5225493).sum := by decide
  have hdescent : baseEnd_5225493 < baseStart_5225493 := by decide
  rcases family_descends (prefixWord ++ tailWord_5225493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5225507 : List Nat := [1, 1, 1, 4, 3, 2, 1, 5, 1, 1, 3]
def baseStart_5225507 : Nat := 118140960795 + 5225507 * 2 ^ 59
def prefixEnd_5225507 : Nat := 4983230072969 + 3 ^ 40 * 5225507 * 2
def baseEnd_5225507 : Nat := 2683196754433991913530837

theorem tailTrace_5225507 : CollatzResearch.WordTrace tailWord_5225507 prefixEnd_5225507 2683196754433991913530837 := by
  unfold tailWord_5225507
  simp only [CollatzResearch.WordTrace]
  refine ⟨190589897879888059389490775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 127059931919925372926327183 190589897879888059389490775)
  ·
    refine ⟨285884846819832089084236163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190589897879888059389490775 285884846819832089084236163)
    ·
      refine ⟨428827270229748133626354245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285884846819832089084236163 428827270229748133626354245)
      ·
        refine ⟨80405113168077775054941421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 428827270229748133626354245 80405113168077775054941421)
        ·
          refine ⟨30151917438029165645603033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80405113168077775054941421 30151917438029165645603033)
          ·
            refine ⟨22613938078521874234202275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30151917438029165645603033 22613938078521874234202275)
            ·
              refine ⟨33920907117782811351303413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22613938078521874234202275 33920907117782811351303413)
              ·
                refine ⟨3180085042292138564184695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33920907117782811351303413 3180085042292138564184695)
                ·
                  refine ⟨4770127563438207846277043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3180085042292138564184695 4770127563438207846277043)
                  ·
                    refine ⟨7155191345157311769415565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4770127563438207846277043 7155191345157311769415565)
                    ·
                      refine ⟨2683196754433991913530837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7155191345157311769415565 2683196754433991913530837)
                      ·
                        rfl

theorem cell23_5225507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 5, 1, 1, 3].length) (baseStart_5225507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5225507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5225507 prefixEnd_5225507 := by exact prefixLift 5225507
  have htrace : WordTrace (prefixWord ++ tailWord_5225507) baseStart_5225507 baseEnd_5225507 := by
    simpa [prefixWord, tailWord_5225507, baseEnd_5225507] using wordTrace_append hprefix tailTrace_5225507
  have hstable : (prefixWord ++ tailWord_5225507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5225507).length < 2 ^ (prefixWord ++ tailWord_5225507).sum := by decide
  have hdescent : baseEnd_5225507 < baseStart_5225507 := by decide
  rcases family_descends (prefixWord ++ tailWord_5225507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
