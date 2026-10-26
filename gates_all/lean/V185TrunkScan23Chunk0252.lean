import V185TrunkScan23Chunk0251

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1490951 : List Nat := [1, 1, 4, 3, 1, 2, 1, 2, 2, 1, 5]
def baseStart_1490951 : Nat := 118140960795 + 1490951 * 2 ^ 59
def prefixEnd_1490951 : Nat := 4983230072969 + 3 ^ 40 * 1490951 * 2
def baseEnd_1490951 : Nat := 765574495301701381055747

theorem tailTrace_1490951 : CollatzResearch.WordTrace tailWord_1490951 prefixEnd_1490951 765574495301701381055747 := by
  unfold tailWord_1490951
  simp only [CollatzResearch.WordTrace]
  refine ⟨54379450421546636003448707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36252966947697757335632471 54379450421546636003448707)
  ·
    refine ⟨81569175632319954005173061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54379450421546636003448707 81569175632319954005173061)
    ·
      refine ⟨15294220431059991375969949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81569175632319954005173061 15294220431059991375969949)
      ·
        refine ⟨5735332661647496765988731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15294220431059991375969949 5735332661647496765988731)
        ·
          refine ⟨8602998992471245148983097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5735332661647496765988731 8602998992471245148983097)
          ·
            refine ⟨6452249244353433861737323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8602998992471245148983097 6452249244353433861737323)
            ·
              refine ⟨9678373866530150792605985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6452249244353433861737323 9678373866530150792605985)
              ·
                refine ⟨7258780399897613094454489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9678373866530150792605985 7258780399897613094454489)
                ·
                  refine ⟨5444085299923209820840867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7258780399897613094454489 5444085299923209820840867)
                  ·
                    refine ⟨8166127949884814731261301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5444085299923209820840867 8166127949884814731261301)
                    ·
                      refine ⟨765574495301701381055747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8166127949884814731261301 765574495301701381055747)
                      ·
                        rfl

theorem cell23_1490951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_1490951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1490951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1490951 prefixEnd_1490951 := by exact prefixLift 1490951
  have htrace : WordTrace (prefixWord ++ tailWord_1490951) baseStart_1490951 baseEnd_1490951 := by
    simpa [prefixWord, tailWord_1490951, baseEnd_1490951] using wordTrace_append hprefix tailTrace_1490951
  have hstable : (prefixWord ++ tailWord_1490951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490951).length < 2 ^ (prefixWord ++ tailWord_1490951).sum := by decide
  have hdescent : baseEnd_1490951 < baseStart_1490951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490965 : List Nat := [1, 3, 2, 1, 5, 1, 1, 2, 1, 4, 2]
def baseStart_1490965 : Nat := 118140960795 + 1490965 * 2 ^ 59
def prefixEnd_1490965 : Nat := 4983230072969 + 3 ^ 40 * 1490965 * 2
def baseEnd_1490965 : Nat := 765581684030864326280683

theorem tailTrace_1490965 : CollatzResearch.WordTrace tailWord_1490965 prefixEnd_1490965 765581684030864326280683 := by
  unfold tailWord_1490965
  simp only [CollatzResearch.WordTrace]
  refine ⟨54379961043495916394458349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36253307362330610929638899 54379961043495916394458349)
  ·
    refine ⟨20392485391310968647921881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54379961043495916394458349 20392485391310968647921881)
    ·
      refine ⟨15294364043483226485941411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20392485391310968647921881 15294364043483226485941411)
      ·
        refine ⟨22941546065224839728912117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15294364043483226485941411 22941546065224839728912117)
        ·
          refine ⟨2150769943614828724585511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22941546065224839728912117 2150769943614828724585511)
          ·
            refine ⟨3226154915422243086878267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2150769943614828724585511 3226154915422243086878267)
            ·
              refine ⟨4839232373133364630317401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3226154915422243086878267 4839232373133364630317401)
              ·
                refine ⟨3629424279850023472738051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4839232373133364630317401 3629424279850023472738051)
                ·
                  refine ⟨5444136419775035209107077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3629424279850023472738051 5444136419775035209107077)
                  ·
                    refine ⟨1020775578707819101707577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5444136419775035209107077 1020775578707819101707577)
                    ·
                      refine ⟨765581684030864326280683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1020775578707819101707577 765581684030864326280683)
                      ·
                        rfl

theorem cell23_1490965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 2, 1, 4, 2].length) (baseStart_1490965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1490965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1490965 prefixEnd_1490965 := by exact prefixLift 1490965
  have htrace : WordTrace (prefixWord ++ tailWord_1490965) baseStart_1490965 baseEnd_1490965 := by
    simpa [prefixWord, tailWord_1490965, baseEnd_1490965] using wordTrace_append hprefix tailTrace_1490965
  have hstable : (prefixWord ++ tailWord_1490965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490965).length < 2 ^ (prefixWord ++ tailWord_1490965).sum := by decide
  have hdescent : baseEnd_1490965 < baseStart_1490965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491058 : List Nat := [3, 2, 1, 2, 2, 2, 1, 2, 1, 4, 3]
def baseStart_1491058 : Nat := 118140960795 + 1491058 * 2 ^ 59
def prefixEnd_1491058 : Nat := 4983230072969 + 3 ^ 40 * 1491058 * 2
def baseEnd_1491058 : Nat := 765629437731732462417755

theorem tailTrace_1491058 : CollatzResearch.WordTrace tailWord_1491058 prefixEnd_1491058 765629437731732462417755 := by
  unfold tailWord_1491058
  simp only [CollatzResearch.WordTrace]
  refine ⟨13595838258039748319398457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36255568688105995518395885 13595838258039748319398457)
  ·
    refine ⟨10196878693529811239548843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13595838258039748319398457 10196878693529811239548843)
    ·
      refine ⟨15295318040294716859323265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10196878693529811239548843 15295318040294716859323265)
      ·
        refine ⟨11471488530221037644492449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15295318040294716859323265 11471488530221037644492449)
        ·
          refine ⟨8603616397665778233369337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11471488530221037644492449 8603616397665778233369337)
          ·
            refine ⟨6452712298249333675027003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8603616397665778233369337 6452712298249333675027003)
            ·
              refine ⟨9679068447374000512540505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6452712298249333675027003 9679068447374000512540505)
              ·
                refine ⟨7259301335530500384405379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9679068447374000512540505 7259301335530500384405379)
                ·
                  refine ⟨10888952003295750576608069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7259301335530500384405379 10888952003295750576608069)
                  ·
                    refine ⟨2041678500617953233114013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10888952003295750576608069 2041678500617953233114013)
                    ·
                      refine ⟨765629437731732462417755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2041678500617953233114013 765629437731732462417755)
                      ·
                        rfl

theorem cell23_1491058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 1, 4, 3].length) (baseStart_1491058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1491058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1491058 prefixEnd_1491058 := by exact prefixLift 1491058
  have htrace : WordTrace (prefixWord ++ tailWord_1491058) baseStart_1491058 baseEnd_1491058 := by
    simpa [prefixWord, tailWord_1491058, baseEnd_1491058] using wordTrace_append hprefix tailTrace_1491058
  have hstable : (prefixWord ++ tailWord_1491058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491058).length < 2 ^ (prefixWord ++ tailWord_1491058).sum := by decide
  have hdescent : baseEnd_1491058 < baseStart_1491058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491082 : List Nat := [3, 1, 2, 3, 1, 2, 3, 3, 1, 4]
def baseStart_1491082 : Nat := 118140960795 + 1491082 * 2 ^ 59
def prefixEnd_1491082 : Nat := 4983230072969 + 3 ^ 40 * 1491082 * 2
def baseEnd_1491082 : Nat := 255213920422480122839215

theorem tailTrace_1491082 : CollatzResearch.WordTrace tailWord_1491082 prefixEnd_1491082 255213920422480122839215 := by
  unfold tailWord_1491082
  simp only [CollatzResearch.WordTrace]
  refine ⟨13596057096018011344116875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36256152256048030250978333 13596057096018011344116875)
  ·
    refine ⟨20394085644027017016175313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13596057096018011344116875 20394085644027017016175313)
    ·
      refine ⟨15295564233020262762131485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20394085644027017016175313 15295564233020262762131485)
      ·
        refine ⟨5735836587382598535799307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15295564233020262762131485 5735836587382598535799307)
        ·
          refine ⟨8603754881073897803698961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5735836587382598535799307 8603754881073897803698961)
          ·
            refine ⟨6452816160805423352774221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8603754881073897803698961 6452816160805423352774221)
            ·
              refine ⟨2419806060302033757290333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6452816160805423352774221 2419806060302033757290333)
              ·
                refine ⟨907427272613262658983875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2419806060302033757290333 907427272613262658983875)
                ·
                  refine ⟨1361140908919893988475813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 907427272613262658983875 1361140908919893988475813)
                  ·
                    refine ⟨255213920422480122839215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1361140908919893988475813 255213920422480122839215)
                    ·
                      rfl

theorem cell23_1491082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 3, 1, 4].length) (baseStart_1491082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1491082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1491082 prefixEnd_1491082 := by exact prefixLift 1491082
  have htrace : WordTrace (prefixWord ++ tailWord_1491082) baseStart_1491082 baseEnd_1491082 := by
    simpa [prefixWord, tailWord_1491082, baseEnd_1491082] using wordTrace_append hprefix tailTrace_1491082
  have hstable : (prefixWord ++ tailWord_1491082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491082).length < 2 ^ (prefixWord ++ tailWord_1491082).sum := by decide
  have hdescent : baseEnd_1491082 < baseStart_1491082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491091 : List Nat := [1, 1, 1, 2, 1, 2, 3, 2, 5, 5]
def baseStart_1491091 : Nat := 118140960795 + 1491091 * 2 ^ 59
def prefixEnd_1491091 : Nat := 4983230072969 + 3 ^ 40 * 1491091 * 2
def baseEnd_1491091 : Nat := 255215460864443611101701

theorem tailTrace_1491091 : CollatzResearch.WordTrace tailWord_1491091 prefixEnd_1491091 255215460864443611101701 := by
  unfold tailWord_1491091
  simp only [CollatzResearch.WordTrace]
  refine ⟨54384556641039439913545127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36256371094026293275696751 54384556641039439913545127)
  ·
    refine ⟨81576834961559159870317691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54384556641039439913545127 81576834961559159870317691)
    ·
      refine ⟨122365252442338739805476537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81576834961559159870317691 122365252442338739805476537)
      ·
        refine ⟨91773939331754054854107403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122365252442338739805476537 91773939331754054854107403)
        ·
          refine ⟨137660908997631082281161105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91773939331754054854107403 137660908997631082281161105)
          ·
            refine ⟨103245681748223311710870829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137660908997631082281161105 103245681748223311710870829)
            ·
              refine ⟨38717130655583741891576561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 103245681748223311710870829 38717130655583741891576561)
              ·
                refine ⟨29037847991687806418682421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38717130655583741891576561 29037847991687806418682421)
                ·
                  refine ⟨2722298249220731851751477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29037847991687806418682421 2722298249220731851751477)
                  ·
                    refine ⟨255215460864443611101701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2722298249220731851751477 255215460864443611101701)
                    ·
                      rfl

theorem cell23_1491091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 5, 5].length) (baseStart_1491091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1491091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1491091 prefixEnd_1491091 := by exact prefixLift 1491091
  have htrace : WordTrace (prefixWord ++ tailWord_1491091) baseStart_1491091 baseEnd_1491091 := by
    simpa [prefixWord, tailWord_1491091, baseEnd_1491091] using wordTrace_append hprefix tailTrace_1491091
  have hstable : (prefixWord ++ tailWord_1491091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491091).length < 2 ^ (prefixWord ++ tailWord_1491091).sum := by decide
  have hdescent : baseEnd_1491091 < baseStart_1491091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491128 : List Nat := [2, 1, 2, 1, 2, 1, 5, 1, 3, 1, 4]
def baseStart_1491128 : Nat := 118140960795 + 1491128 * 2 ^ 59
def prefixEnd_1491128 : Nat := 4983230072969 + 3 ^ 40 * 1491128 * 2
def baseEnd_1491128 : Nat := 765665381377547188542433

theorem tailTrace_1491128 : CollatzResearch.WordTrace tailWord_1491128 prefixEnd_1491128 765665381377547188542433 := by
  unfold tailWord_1491128
  simp only [CollatzResearch.WordTrace]
  refine ⟨27192953070952697616321019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36257270761270263488428025 27192953070952697616321019)
  ·
    refine ⟨40789429606429046424481529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27192953070952697616321019 40789429606429046424481529)
    ·
      refine ⟨30592072204821784818361147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40789429606429046424481529 30592072204821784818361147)
      ·
        refine ⟨45888108307232677227541721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30592072204821784818361147 45888108307232677227541721)
        ·
          refine ⟨34416081230424507920656291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45888108307232677227541721 34416081230424507920656291)
          ·
            refine ⟨51624121845636761880984437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34416081230424507920656291 51624121845636761880984437)
            ·
              refine ⟨4839761423028446426342291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51624121845636761880984437 4839761423028446426342291)
              ·
                refine ⟨7259642134542669639513437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4839761423028446426342291 7259642134542669639513437)
                ·
                  refine ⟨2722365800453501114817539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7259642134542669639513437 2722365800453501114817539)
                  ·
                    refine ⟨4083548700680251672226309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2722365800453501114817539 4083548700680251672226309)
                    ·
                      refine ⟨765665381377547188542433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4083548700680251672226309 765665381377547188542433)
                      ·
                        rfl

theorem cell23_1491128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 3, 1, 4].length) (baseStart_1491128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1491128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1491128 prefixEnd_1491128 := by exact prefixLift 1491128
  have htrace : WordTrace (prefixWord ++ tailWord_1491128) baseStart_1491128 baseEnd_1491128 := by
    simpa [prefixWord, tailWord_1491128, baseEnd_1491128] using wordTrace_append hprefix tailTrace_1491128
  have hstable : (prefixWord ++ tailWord_1491128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491128).length < 2 ^ (prefixWord ++ tailWord_1491128).sum := by decide
  have hdescent : baseEnd_1491128 < baseStart_1491128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491145 : List Nat := [1, 2, 1, 1, 2, 1, 1, 3, 7, 2, 2]
def baseStart_1491145 : Nat := 118140960795 + 1491145 * 2 ^ 59
def prefixEnd_1491145 : Nat := 4983230072969 + 3 ^ 40 * 1491145 * 2
def baseEnd_1491145 : Nat := 765674110548673622029855

theorem tailTrace_1491145 : CollatzResearch.WordTrace tailWord_1491145 prefixEnd_1491145 765674110548673622029855 := by
  unfold tailWord_1491145
  simp only [CollatzResearch.WordTrace]
  refine ⟨54386526182843807136010889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36257684121895871424007259 54386526182843807136010889)
  ·
    refine ⟨40789894637132855352008167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54386526182843807136010889 40789894637132855352008167)
    ·
      refine ⟨61184841955699283028012251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40789894637132855352008167 61184841955699283028012251)
      ·
        refine ⟨91777262933548924542018377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61184841955699283028012251 91777262933548924542018377)
        ·
          refine ⟨68832947200161693406513783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91777262933548924542018377 68832947200161693406513783)
          ·
            refine ⟨103249420800242540109770675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68832947200161693406513783 103249420800242540109770675)
            ·
              refine ⟨154874131200363810164656013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103249420800242540109770675 154874131200363810164656013)
              ·
                refine ⟨58077799200136428811746005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 154874131200363810164656013 58077799200136428811746005)
                ·
                  refine ⟨1361198418753197550275297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 58077799200136428811746005 1361198418753197550275297)
                  ·
                    refine ⟨1020898814064898162706473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1361198418753197550275297 1020898814064898162706473)
                    ·
                      refine ⟨765674110548673622029855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1020898814064898162706473 765674110548673622029855)
                      ·
                        rfl

theorem cell23_1491145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 7, 2, 2].length) (baseStart_1491145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1491145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1491145 prefixEnd_1491145 := by exact prefixLift 1491145
  have htrace : WordTrace (prefixWord ++ tailWord_1491145) baseStart_1491145 baseEnd_1491145 := by
    simpa [prefixWord, tailWord_1491145, baseEnd_1491145] using wordTrace_append hprefix tailTrace_1491145
  have hstable : (prefixWord ++ tailWord_1491145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491145).length < 2 ^ (prefixWord ++ tailWord_1491145).sum := by decide
  have hdescent : baseEnd_1491145 < baseStart_1491145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491175 : List Nat := [1, 1, 5, 3, 1, 1, 1, 3, 1, 2, 4]
def baseStart_1491175 : Nat := 118140960795 + 1491175 * 2 ^ 59
def prefixEnd_1491175 : Nat := 4983230072969 + 3 ^ 40 * 1491175 * 2
def baseEnd_1491175 : Nat := 765689514968308504654717

theorem tailTrace_1491175 : CollatzResearch.WordTrace tailWord_1491175 prefixEnd_1491175 765689514968308504654717 := by
  unfold tailWord_1491175
  simp only [CollatzResearch.WordTrace]
  refine ⟨54387620372735122259602979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36258413581823414839735319 54387620372735122259602979)
  ·
    refine ⟨81581430559102683389404469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54387620372735122259602979 81581430559102683389404469)
    ·
      refine ⟨7648259114915876567756669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81581430559102683389404469 7648259114915876567756669)
      ·
        refine ⟨2868097168093453712908751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7648259114915876567756669 2868097168093453712908751)
        ·
          refine ⟨4302145752140180569363127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2868097168093453712908751 4302145752140180569363127)
          ·
            refine ⟨6453218628210270854044691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4302145752140180569363127 6453218628210270854044691)
            ·
              refine ⟨9679827942315406281067037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6453218628210270854044691 9679827942315406281067037)
              ·
                refine ⟨3629935478368277355400139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9679827942315406281067037 3629935478368277355400139)
                ·
                  refine ⟨5444903217552416033100209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3629935478368277355400139 5444903217552416033100209)
                  ·
                    refine ⟨4083677413164312024825157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5444903217552416033100209 4083677413164312024825157)
                    ·
                      refine ⟨765689514968308504654717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4083677413164312024825157 765689514968308504654717)
                      ·
                        rfl

theorem cell23_1491175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_1491175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1491175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1491175 prefixEnd_1491175 := by exact prefixLift 1491175
  have htrace : WordTrace (prefixWord ++ tailWord_1491175) baseStart_1491175 baseEnd_1491175 := by
    simpa [prefixWord, tailWord_1491175, baseEnd_1491175] using wordTrace_append hprefix tailTrace_1491175
  have hstable : (prefixWord ++ tailWord_1491175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491175).length < 2 ^ (prefixWord ++ tailWord_1491175).sum := by decide
  have hdescent : baseEnd_1491175 < baseStart_1491175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491196 : List Nat := [2, 2, 2, 1, 4, 2, 2, 3, 1, 2, 2]
def baseStart_1491196 : Nat := 118140960795 + 1491196 * 2 ^ 59
def prefixEnd_1491196 : Nat := 4983230072969 + 3 ^ 40 * 1491196 * 2
def baseEnd_1491196 : Nat := 765700298062052922492121

theorem tailTrace_1491196 : CollatzResearch.WordTrace tailWord_1491196 prefixEnd_1491196 765700298062052922492121 := by
  unfold tailWord_1491196
  simp only [CollatzResearch.WordTrace]
  refine ⟨27194193152829521423058721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36258924203772695230744961 27194193152829521423058721)
  ·
    refine ⟨20395644864622141067294041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27194193152829521423058721 20395644864622141067294041)
    ·
      refine ⟨15296733648466605800470531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20395644864622141067294041 15296733648466605800470531)
      ·
        refine ⟨22945100472699908700705797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15296733648466605800470531 22945100472699908700705797)
        ·
          refine ⟨4302206338631232881382337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22945100472699908700705797 4302206338631232881382337)
          ·
            refine ⟨3226654753973424661036753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4302206338631232881382337 3226654753973424661036753)
            ·
              refine ⟨2419991065480068495777565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3226654753973424661036753 2419991065480068495777565)
              ·
                refine ⟨907496649555025685916587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2419991065480068495777565 907496649555025685916587)
                ·
                  refine ⟨1361244974332538528874881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 907496649555025685916587 1361244974332538528874881)
                  ·
                    refine ⟨1020933730749403896656161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1361244974332538528874881 1020933730749403896656161)
                    ·
                      refine ⟨765700298062052922492121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1020933730749403896656161 765700298062052922492121)
                      ·
                        rfl

theorem cell23_1491196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 3, 1, 2, 2].length) (baseStart_1491196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1491196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1491196 prefixEnd_1491196 := by exact prefixLift 1491196
  have htrace : WordTrace (prefixWord ++ tailWord_1491196) baseStart_1491196 baseEnd_1491196 := by
    simpa [prefixWord, tailWord_1491196, baseEnd_1491196] using wordTrace_append hprefix tailTrace_1491196
  have hstable : (prefixWord ++ tailWord_1491196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491196).length < 2 ^ (prefixWord ++ tailWord_1491196).sum := by decide
  have hdescent : baseEnd_1491196 < baseStart_1491196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491205 : List Nat := [1, 3, 1, 1, 2, 1, 2, 2, 5, 3, 2]
def baseStart_1491205 : Nat := 118140960795 + 1491205 * 2 ^ 59
def prefixEnd_1491205 : Nat := 4983230072969 + 3 ^ 40 * 1491205 * 2
def baseEnd_1491205 : Nat := 765704919387943387279579

theorem tailTrace_1491205 : CollatzResearch.WordTrace tailWord_1491205 prefixEnd_1491205 765704919387943387279579 := by
  unfold tailWord_1491205
  simp only [CollatzResearch.WordTrace]
  refine ⟨54388714562626437383195069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36259143041750958255463379 54388714562626437383195069)
  ·
    refine ⟨20395767960984914018698151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54388714562626437383195069 20395767960984914018698151)
    ·
      refine ⟨30593651941477371028047227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20395767960984914018698151 30593651941477371028047227)
      ·
        refine ⟨45890477912216056542070841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30593651941477371028047227 45890477912216056542070841)
        ·
          refine ⟨34417858434162042406553131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45890477912216056542070841 34417858434162042406553131)
          ·
            refine ⟨51626787651243063609829697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34417858434162042406553131 51626787651243063609829697)
            ·
              refine ⟨38720090738432297707372273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51626787651243063609829697 38720090738432297707372273)
              ·
                refine ⟨29040068053824223280529205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38720090738432297707372273 29040068053824223280529205)
                ·
                  refine ⟨2722506380046020932549613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29040068053824223280529205 2722506380046020932549613)
                  ·
                    refine ⟨1020939892517257849706105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2722506380046020932549613 1020939892517257849706105)
                    ·
                      refine ⟨765704919387943387279579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1020939892517257849706105 765704919387943387279579)
                      ·
                        rfl

theorem cell23_1491205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 5, 3, 2].length) (baseStart_1491205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1491205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1491205 prefixEnd_1491205 := by exact prefixLift 1491205
  have htrace : WordTrace (prefixWord ++ tailWord_1491205) baseStart_1491205 baseEnd_1491205 := by
    simpa [prefixWord, tailWord_1491205, baseEnd_1491205] using wordTrace_append hprefix tailTrace_1491205
  have hstable : (prefixWord ++ tailWord_1491205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491205).length < 2 ^ (prefixWord ++ tailWord_1491205).sum := by decide
  have hdescent : baseEnd_1491205 < baseStart_1491205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491229 : List Nat := [1, 4, 2, 3, 2, 2, 1, 1, 1, 3, 3]
def baseStart_1491229 : Nat := 118140960795 + 1491229 * 2 ^ 59
def prefixEnd_1491229 : Nat := 4983230072969 + 3 ^ 40 * 1491229 * 2
def baseEnd_1491229 : Nat := 765717242923651293379469

theorem tailTrace_1491229 : CollatzResearch.WordTrace tailWord_1491229 prefixEnd_1491229 765717242923651293379469 := by
  unfold tailWord_1491229
  simp only [CollatzResearch.WordTrace]
  refine ⟨54389589914539489482068741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36259726609692992988045827 54389589914539489482068741)
  ·
    refine ⟨10198048108976154277887889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54389589914539489482068741 10198048108976154277887889)
    ·
      refine ⟨7648536081732115708415917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10198048108976154277887889 7648536081732115708415917)
      ·
        refine ⟨2868201030649543390655969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7648536081732115708415917 2868201030649543390655969)
        ·
          refine ⟨2151150772987157542991977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2868201030649543390655969 2151150772987157542991977)
          ·
            refine ⟨1613363079740368157243983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2151150772987157542991977 1613363079740368157243983)
            ·
              refine ⟨2420044619610552235865975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1613363079740368157243983 2420044619610552235865975)
              ·
                refine ⟨3630066929415828353798963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2420044619610552235865975 3630066929415828353798963)
                ·
                  refine ⟨5445100394123742530698445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3630066929415828353798963 5445100394123742530698445)
                  ·
                    refine ⟨2041912647796403449011917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5445100394123742530698445 2041912647796403449011917)
                    ·
                      refine ⟨765717242923651293379469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2041912647796403449011917 765717242923651293379469)
                      ·
                        rfl

theorem cell23_1491229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_1491229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1491229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1491229 prefixEnd_1491229 := by exact prefixLift 1491229
  have htrace : WordTrace (prefixWord ++ tailWord_1491229) baseStart_1491229 baseEnd_1491229 := by
    simpa [prefixWord, tailWord_1491229, baseEnd_1491229] using wordTrace_append hprefix tailTrace_1491229
  have hstable : (prefixWord ++ tailWord_1491229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491229).length < 2 ^ (prefixWord ++ tailWord_1491229).sum := by decide
  have hdescent : baseEnd_1491229 < baseStart_1491229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491248 : List Nat := [2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 4]
def baseStart_1491248 : Nat := 118140960795 + 1491248 * 2 ^ 59
def prefixEnd_1491248 : Nat := 4983230072969 + 3 ^ 40 * 1491248 * 2
def baseEnd_1491248 : Nat := 765726999056086719041881

theorem tailTrace_1491248 : CollatzResearch.WordTrace tailWord_1491248 prefixEnd_1491248 765726999056086719041881 := by
  unfold tailWord_1491248
  simp only [CollatzResearch.WordTrace]
  refine ⟨27195141450735327863505199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36260188600980437151340265 27195141450735327863505199)
  ·
    refine ⟨40792712176102991795257799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27195141450735327863505199 40792712176102991795257799)
    ·
      refine ⟨61189068264154487692886699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40792712176102991795257799 61189068264154487692886699)
      ·
        refine ⟨91783602396231731539330049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61189068264154487692886699 91783602396231731539330049)
        ·
          refine ⟨68837701797173798654497537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91783602396231731539330049 68837701797173798654497537)
          ·
            refine ⟨51628276347880348990873153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68837701797173798654497537 51628276347880348990873153)
            ·
              refine ⟨38721207260910261743154865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51628276347880348990873153 38721207260910261743154865)
              ·
                refine ⟨29040905445682696307366149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38721207260910261743154865 29040905445682696307366149)
                ·
                  refine ⟨5445169771065505557631153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29040905445682696307366149 5445169771065505557631153)
                  ·
                    refine ⟨4083877328299129168223365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5445169771065505557631153 4083877328299129168223365)
                    ·
                      refine ⟨765726999056086719041881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4083877328299129168223365 765726999056086719041881)
                      ·
                        rfl

theorem cell23_1491248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 4].length) (baseStart_1491248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1491248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1491248 prefixEnd_1491248 := by exact prefixLift 1491248
  have htrace : WordTrace (prefixWord ++ tailWord_1491248) baseStart_1491248 baseEnd_1491248 := by
    simpa [prefixWord, tailWord_1491248, baseEnd_1491248] using wordTrace_append hprefix tailTrace_1491248
  have hstable : (prefixWord ++ tailWord_1491248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491248).length < 2 ^ (prefixWord ++ tailWord_1491248).sum := by decide
  have hdescent : baseEnd_1491248 < baseStart_1491248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491278 : List Nat := [4, 1, 1, 1, 1, 1, 2, 1, 2, 1, 8]
def baseStart_1491278 : Nat := 118140960795 + 1491278 * 2 ^ 59
def prefixEnd_1491278 : Nat := 4983230072969 + 3 ^ 40 * 1491278 * 2
def baseEnd_1491278 : Nat := 765742403475721601666743

theorem tailTrace_1491278 : CollatzResearch.WordTrace tailWord_1491278 prefixEnd_1491278 765742403475721601666743 := by
  unfold tailWord_1491278
  simp only [CollatzResearch.WordTrace]
  refine ⟨6798922136420246356325311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36260918060907980567068325 6798922136420246356325311)
  ·
    refine ⟨10198383204630369534487967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6798922136420246356325311 10198383204630369534487967)
    ·
      refine ⟨15297574806945554301731951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10198383204630369534487967 15297574806945554301731951)
      ·
        refine ⟨22946362210418331452597927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15297574806945554301731951 22946362210418331452597927)
        ·
          refine ⟨34419543315627497178896891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22946362210418331452597927 34419543315627497178896891)
          ·
            refine ⟨51629314973441245768345337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34419543315627497178896891 51629314973441245768345337)
            ·
              refine ⟨38721986230080934326259003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51629314973441245768345337 38721986230080934326259003)
              ·
                refine ⟨58082979345121401489388505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38721986230080934326259003 58082979345121401489388505)
                ·
                  refine ⟨43562234508841051117041379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58082979345121401489388505 43562234508841051117041379)
                  ·
                    refine ⟨65343351763261576675562069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43562234508841051117041379 65343351763261576675562069)
                    ·
                      refine ⟨765742403475721601666743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 65343351763261576675562069 765742403475721601666743)
                      ·
                        rfl

theorem cell23_1491278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_1491278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1491278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1491278 prefixEnd_1491278 := by exact prefixLift 1491278
  have htrace : WordTrace (prefixWord ++ tailWord_1491278) baseStart_1491278 baseEnd_1491278 := by
    simpa [prefixWord, tailWord_1491278, baseEnd_1491278] using wordTrace_append hprefix tailTrace_1491278
  have hstable : (prefixWord ++ tailWord_1491278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491278).length < 2 ^ (prefixWord ++ tailWord_1491278).sum := by decide
  have hdescent : baseEnd_1491278 < baseStart_1491278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491288 : List Nat := [2, 1, 2, 2, 1, 1, 2, 4, 1, 7]
def baseStart_1491288 : Nat := 118140960795 + 1491288 * 2 ^ 59
def prefixEnd_1491288 : Nat := 4983230072969 + 3 ^ 40 * 1491288 * 2
def baseEnd_1491288 : Nat := 255249179427422187513899

theorem tailTrace_1491288 : CollatzResearch.WordTrace tailWord_1491288 prefixEnd_1491288 255249179427422187513899 := by
  unfold tailWord_1491288
  simp only [CollatzResearch.WordTrace]
  refine ⟨27195870910662871279233259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36261161214217161705644345 27195870910662871279233259)
  ·
    refine ⟨40793806365994306918849889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27195870910662871279233259 40793806365994306918849889)
    ·
      refine ⟨30595354774495730189137417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40793806365994306918849889 30595354774495730189137417)
      ·
        refine ⟨22946516080871797641853063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30595354774495730189137417 22946516080871797641853063)
        ·
          refine ⟨34419774121307696462779595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22946516080871797641853063 34419774121307696462779595)
          ·
            refine ⟨51629661181961544694169393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34419774121307696462779595 51629661181961544694169393)
            ·
              refine ⟨38722245886471158520627045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51629661181961544694169393 38722245886471158520627045)
              ·
                refine ⟨7260421103713342222617571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38722245886471158520627045 7260421103713342222617571)
                ·
                  refine ⟨10890631655570013333926357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7260421103713342222617571 10890631655570013333926357)
                  ·
                    refine ⟨255249179427422187513899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10890631655570013333926357 255249179427422187513899)
                    ·
                      rfl

theorem cell23_1491288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 1, 7].length) (baseStart_1491288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1491288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1491288 prefixEnd_1491288 := by exact prefixLift 1491288
  have htrace : WordTrace (prefixWord ++ tailWord_1491288) baseStart_1491288 baseEnd_1491288 := by
    simpa [prefixWord, tailWord_1491288, baseEnd_1491288] using wordTrace_append hprefix tailTrace_1491288
  have hstable : (prefixWord ++ tailWord_1491288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491288).length < 2 ^ (prefixWord ++ tailWord_1491288).sum := by decide
  have hdescent : baseEnd_1491288 < baseStart_1491288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491305 : List Nat := [1, 2, 1, 1, 1, 3, 6, 1, 2, 5]
def baseStart_1491305 : Nat := 118140960795 + 1491305 * 2 ^ 59
def prefixEnd_1491305 : Nat := 4983230072969 + 3 ^ 40 * 1491305 * 2
def baseEnd_1491305 : Nat := 255252089151130998676373

theorem tailTrace_1491305 : CollatzResearch.WordTrace tailWord_1491305 prefixEnd_1491305 255252089151130998676373 := by
  unfold tailWord_1491305
  simp only [CollatzResearch.WordTrace]
  refine ⟨54392361862264154461835369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36261574574842769641223579 54392361862264154461835369)
  ·
    refine ⟨40794271396698115846376527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54392361862264154461835369 40794271396698115846376527)
    ·
      refine ⟨61191407095047173769564791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40794271396698115846376527 61191407095047173769564791)
      ·
        refine ⟨91787110642570760654347187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61191407095047173769564791 91787110642570760654347187)
        ·
          refine ⟨137680665963856140981520781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91787110642570760654347187 137680665963856140981520781)
          ·
            refine ⟨51630249736446052868070293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137680665963856140981520781 51630249736446052868070293)
            ·
              refine ⟨2420167956395908728190795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 51630249736446052868070293 2420167956395908728190795)
              ·
                refine ⟨3630251934593863092286193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2420167956395908728190795 3630251934593863092286193)
                ·
                  refine ⟨2722688950945397319214645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3630251934593863092286193 2722688950945397319214645)
                  ·
                    refine ⟨255252089151130998676373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2722688950945397319214645 255252089151130998676373)
                    ·
                      rfl

theorem cell23_1491305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 1, 2, 5].length) (baseStart_1491305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1491305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1491305 prefixEnd_1491305 := by exact prefixLift 1491305
  have htrace : WordTrace (prefixWord ++ tailWord_1491305) baseStart_1491305 baseEnd_1491305 := by
    simpa [prefixWord, tailWord_1491305, baseEnd_1491305] using wordTrace_append hprefix tailTrace_1491305
  have hstable : (prefixWord ++ tailWord_1491305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491305).length < 2 ^ (prefixWord ++ tailWord_1491305).sum := by decide
  have hdescent : baseEnd_1491305 < baseStart_1491305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491352 : List Nat := [2, 1, 2, 5, 1, 1, 1, 1, 5, 4]
def baseStart_1491352 : Nat := 118140960795 + 1491352 * 2 ^ 59
def prefixEnd_1491352 : Nat := 4983230072969 + 3 ^ 40 * 1491352 * 2
def baseEnd_1491352 : Nat := 255260133681384770713801

theorem tailTrace_1491352 : CollatzResearch.WordTrace tailWord_1491352 prefixEnd_1491352 255260133681384770713801 := by
  unfold tailWord_1491352
  simp only [CollatzResearch.WordTrace]
  refine ⟨27197038046546940744398155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36262717395395920992530873 27197038046546940744398155)
  ·
    refine ⟨40795557069820411116597233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27197038046546940744398155 40795557069820411116597233)
    ·
      refine ⟨30596667802365308337447925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40795557069820411116597233 30596667802365308337447925)
      ·
        refine ⟨2868437606471747656635743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30596667802365308337447925 2868437606471747656635743)
        ·
          refine ⟨4302656409707621484953615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2868437606471747656635743 4302656409707621484953615)
          ·
            refine ⟨6453984614561432227430423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4302656409707621484953615 6453984614561432227430423)
            ·
              refine ⟨9680976921842148341145635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6453984614561432227430423 9680976921842148341145635)
              ·
                refine ⟨14521465382763222511718453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9680976921842148341145635 14521465382763222511718453)
                ·
                  refine ⟨1361387379634052110473605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14521465382763222511718453 1361387379634052110473605)
                  ·
                    refine ⟨255260133681384770713801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1361387379634052110473605 255260133681384770713801)
                    ·
                      rfl

theorem cell23_1491352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 5, 4].length) (baseStart_1491352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1491352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1491352 prefixEnd_1491352 := by exact prefixLift 1491352
  have htrace : WordTrace (prefixWord ++ tailWord_1491352) baseStart_1491352 baseEnd_1491352 := by
    simpa [prefixWord, tailWord_1491352, baseEnd_1491352] using wordTrace_append hprefix tailTrace_1491352
  have hstable : (prefixWord ++ tailWord_1491352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491352).length < 2 ^ (prefixWord ++ tailWord_1491352).sum := by decide
  have hdescent : baseEnd_1491352 < baseStart_1491352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491362 : List Nat := [3, 3, 1, 2, 1, 1, 3, 1, 1, 4, 3]
def baseStart_1491362 : Nat := 118140960795 + 1491362 * 2 ^ 59
def prefixEnd_1491362 : Nat := 4983230072969 + 3 ^ 40 * 1491362 * 2
def baseEnd_1491362 : Nat := 765785535850699273016357

theorem tailTrace_1491362 : CollatzResearch.WordTrace tailWord_1491362 prefixEnd_1491362 765785535850699273016357 := by
  unfold tailWord_1491362
  simp only [CollatzResearch.WordTrace]
  refine ⟨13598610205764413299165085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36262960548705102131106893 13598610205764413299165085)
  ·
    refine ⟨5099478827161654987186907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13598610205764413299165085 5099478827161654987186907)
    ·
      refine ⟨7649218240742482480780361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5099478827161654987186907 7649218240742482480780361)
      ·
        refine ⟨5736913680556861860585271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7649218240742482480780361 5736913680556861860585271)
        ·
          refine ⟨8605370520835292790877907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5736913680556861860585271 8605370520835292790877907)
          ·
            refine ⟨12908055781252939186316861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8605370520835292790877907 12908055781252939186316861)
            ·
              refine ⟨4840520917969852194868823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12908055781252939186316861 4840520917969852194868823)
              ·
                refine ⟨7260781376954778292303235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4840520917969852194868823 7260781376954778292303235)
                ·
                  refine ⟨10891172065432167438454853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7260781376954778292303235 10891172065432167438454853)
                  ·
                    refine ⟨2042094762268531394710285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10891172065432167438454853 2042094762268531394710285)
                    ·
                      refine ⟨765785535850699273016357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2042094762268531394710285 765785535850699273016357)
                      ·
                        rfl

theorem cell23_1491362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_1491362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1491362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1491362 prefixEnd_1491362 := by exact prefixLift 1491362
  have htrace : WordTrace (prefixWord ++ tailWord_1491362) baseStart_1491362 baseEnd_1491362 := by
    simpa [prefixWord, tailWord_1491362, baseEnd_1491362] using wordTrace_append hprefix tailTrace_1491362
  have hstable : (prefixWord ++ tailWord_1491362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491362).length < 2 ^ (prefixWord ++ tailWord_1491362).sum := by decide
  have hdescent : baseEnd_1491362 < baseStart_1491362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491385 : List Nat := [1, 2, 1, 4, 3, 1, 1, 1, 1, 2, 6]
def baseStart_1491385 : Nat := 118140960795 + 1491385 * 2 ^ 59
def prefixEnd_1491385 : Nat := 4983230072969 + 3 ^ 40 * 1491385 * 2
def baseEnd_1491385 : Nat := 765797345905752683028751

theorem tailTrace_1491385 : CollatzResearch.WordTrace tailWord_1491385 prefixEnd_1491385 765797345905752683028751 := by
  unfold tailWord_1491385
  simp only [CollatzResearch.WordTrace]
  refine ⟨54395279701974328124747609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36263519801316218749831739 54395279701974328124747609)
  ·
    refine ⟨40796459776480746093560707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54395279701974328124747609 40796459776480746093560707)
    ·
      refine ⟨61194689664721119140341061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40796459776480746093560707 61194689664721119140341061)
      ·
        refine ⟨11474004312135209838813949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61194689664721119140341061 11474004312135209838813949)
        ·
          refine ⟨4302751617050703689555231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11474004312135209838813949 4302751617050703689555231)
          ·
            refine ⟨6454127425576055534332847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4302751617050703689555231 6454127425576055534332847)
            ·
              refine ⟨9681191138364083301499271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6454127425576055534332847 9681191138364083301499271)
              ·
                refine ⟨14521786707546124952248907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9681191138364083301499271 14521786707546124952248907)
                ·
                  refine ⟨21782680061319187428373361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14521786707546124952248907 21782680061319187428373361)
                  ·
                    refine ⟨16337010045989390571280021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21782680061319187428373361 16337010045989390571280021)
                    ·
                      refine ⟨765797345905752683028751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16337010045989390571280021 765797345905752683028751)
                      ·
                        rfl

theorem cell23_1491385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_1491385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1491385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1491385 prefixEnd_1491385 := by exact prefixLift 1491385
  have htrace : WordTrace (prefixWord ++ tailWord_1491385) baseStart_1491385 baseEnd_1491385 := by
    simpa [prefixWord, tailWord_1491385, baseEnd_1491385] using wordTrace_append hprefix tailTrace_1491385
  have hstable : (prefixWord ++ tailWord_1491385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491385).length < 2 ^ (prefixWord ++ tailWord_1491385).sum := by decide
  have hdescent : baseEnd_1491385 < baseStart_1491385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491402 : List Nat := [3, 1, 2, 1, 2, 2, 1, 1, 3, 5, 2]
def baseStart_1491402 : Nat := 118140960795 + 1491402 * 2 ^ 59
def prefixEnd_1491402 : Nat := 4983230072969 + 3 ^ 40 * 1491402 * 2
def baseEnd_1491402 : Nat := 765806075076879116516173

theorem tailTrace_1491402 : CollatzResearch.WordTrace tailWord_1491402 prefixEnd_1491402 765806075076879116516173 := by
  unfold tailWord_1491402
  simp only [CollatzResearch.WordTrace]
  refine ⟨13598974935728185007029115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36263933161941826685410973 13598974935728185007029115)
  ·
    refine ⟨20398462403592277510543673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13598974935728185007029115 20398462403592277510543673)
    ·
      refine ⟨15298846802694208132907755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20398462403592277510543673 15298846802694208132907755)
      ·
        refine ⟨22948270204041312199361633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15298846802694208132907755 22948270204041312199361633)
        ·
          refine ⟨17211202653030984149521225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22948270204041312199361633 17211202653030984149521225)
          ·
            refine ⟨12908401989773238112140919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17211202653030984149521225 12908401989773238112140919)
            ·
              refine ⟨19362602984659857168211379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12908401989773238112140919 19362602984659857168211379)
              ·
                refine ⟨29043904476989785752317069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19362602984659857168211379 29043904476989785752317069)
                ·
                  refine ⟨10891464178871169657118901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29043904476989785752317069 10891464178871169657118901)
                  ·
                    refine ⟨1021074766769172155354897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10891464178871169657118901 1021074766769172155354897)
                    ·
                      refine ⟨765806075076879116516173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1021074766769172155354897 765806075076879116516173)
                      ·
                        rfl

theorem cell23_1491402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 3, 5, 2].length) (baseStart_1491402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1491402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1491402 prefixEnd_1491402 := by exact prefixLift 1491402
  have htrace : WordTrace (prefixWord ++ tailWord_1491402) baseStart_1491402 baseEnd_1491402 := by
    simpa [prefixWord, tailWord_1491402, baseEnd_1491402] using wordTrace_append hprefix tailTrace_1491402
  have hstable : (prefixWord ++ tailWord_1491402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491402).length < 2 ^ (prefixWord ++ tailWord_1491402).sum := by decide
  have hdescent : baseEnd_1491402 < baseStart_1491402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491425 : List Nat := [1, 2, 3, 1, 2, 2, 2, 1, 3, 6]
def baseStart_1491425 : Nat := 118140960795 + 1491425 * 2 ^ 59
def prefixEnd_1491425 : Nat := 4983230072969 + 3 ^ 40 * 1491425 * 2
def baseEnd_1491425 : Nat := 255272628377310842176189

theorem tailTrace_1491425 : CollatzResearch.WordTrace tailWord_1491425 prefixEnd_1491425 255272628377310842176189 := by
  unfold tailWord_1491425
  simp only [CollatzResearch.WordTrace]
  refine ⟨54396738621829414956203729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36264492414552943304135819 54396738621829414956203729)
  ·
    refine ⟨40797553966372061217152797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54396738621829414956203729 40797553966372061217152797)
    ·
      refine ⟨15299082737389522956432299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40797553966372061217152797 15299082737389522956432299)
      ·
        refine ⟨22948624106084284434648449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15299082737389522956432299 22948624106084284434648449)
        ·
          refine ⟨17211468079563213325986337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22948624106084284434648449 17211468079563213325986337)
          ·
            refine ⟨12908601059672409994489753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17211468079563213325986337 12908601059672409994489753)
            ·
              refine ⟨9681450794754307495867315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12908601059672409994489753 9681450794754307495867315)
              ·
                refine ⟨14522176192131461243800973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9681450794754307495867315 14522176192131461243800973)
                ·
                  refine ⟨5445816072049297966425365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14522176192131461243800973 5445816072049297966425365)
                  ·
                    refine ⟨255272628377310842176189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5445816072049297966425365 255272628377310842176189)
                    ·
                      rfl

theorem cell23_1491425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 3, 6].length) (baseStart_1491425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1491425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1491425 prefixEnd_1491425 := by exact prefixLift 1491425
  have htrace : WordTrace (prefixWord ++ tailWord_1491425) baseStart_1491425 baseEnd_1491425 := by
    simpa [prefixWord, tailWord_1491425, baseEnd_1491425] using wordTrace_append hprefix tailTrace_1491425
  have hstable : (prefixWord ++ tailWord_1491425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491425).length < 2 ^ (prefixWord ++ tailWord_1491425).sum := by decide
  have hdescent : baseEnd_1491425 < baseStart_1491425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491452 : List Nat := [2, 2, 2, 1, 2, 1, 1, 4, 3, 2, 3]
def baseStart_1491452 : Nat := 118140960795 + 1491452 * 2 ^ 59
def prefixEnd_1491452 : Nat := 4983230072969 + 3 ^ 40 * 1491452 * 2
def baseEnd_1491452 : Nat := 765831749109603920890943

theorem tailTrace_1491452 : CollatzResearch.WordTrace tailWord_1491452 prefixEnd_1491452 765831749109603920890943 := by
  unfold tailWord_1491452
  simp only [CollatzResearch.WordTrace]
  refine ⟨27198861696365799283718305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36265148928487732378291073 27198861696365799283718305)
  ·
    refine ⟨20399146272274349462788729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27198861696365799283718305 20399146272274349462788729)
    ·
      refine ⟨15299359704205762097091547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20399146272274349462788729 15299359704205762097091547)
      ·
        refine ⟨22949039556308643145637321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15299359704205762097091547 22949039556308643145637321)
        ·
          refine ⟨17211779667231482359227991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22949039556308643145637321 17211779667231482359227991)
          ·
            refine ⟨25817669500847223538841987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17211779667231482359227991 25817669500847223538841987)
            ·
              refine ⟨38726504251270835308262981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25817669500847223538841987 38726504251270835308262981)
              ·
                refine ⟨7261219547113281620299309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38726504251270835308262981 7261219547113281620299309)
                ·
                  refine ⟨2722957330167480607612241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7261219547113281620299309 2722957330167480607612241)
                  ·
                    refine ⟨2042217997625610455709181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2722957330167480607612241 2042217997625610455709181)
                    ·
                      refine ⟨765831749109603920890943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2042217997625610455709181 765831749109603920890943)
                      ·
                        rfl

theorem cell23_1491452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 3, 2, 3].length) (baseStart_1491452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1491452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1491452 prefixEnd_1491452 := by exact prefixLift 1491452
  have htrace : WordTrace (prefixWord ++ tailWord_1491452) baseStart_1491452 baseEnd_1491452 := by
    simpa [prefixWord, tailWord_1491452, baseEnd_1491452] using wordTrace_append hprefix tailTrace_1491452
  have hstable : (prefixWord ++ tailWord_1491452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491452).length < 2 ^ (prefixWord ++ tailWord_1491452).sum := by decide
  have hdescent : baseEnd_1491452 < baseStart_1491452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491455 : List Nat := [1, 1, 2, 2, 1, 2, 6, 8]
def baseStart_1491455 : Nat := 118140960795 + 1491455 * 2 ^ 59
def prefixEnd_1491455 : Nat := 4983230072969 + 3 ^ 40 * 1491455 * 2
def baseEnd_1491455 : Nat := 28364195909317311450127

theorem tailTrace_1491455 : CollatzResearch.WordTrace tailWord_1491455 prefixEnd_1491455 28364195909317311450127 := by
  unfold tailWord_1491455
  simp only [CollatzResearch.WordTrace]
  refine ⟨54397832811720730079795819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36265221874480486719863879 54397832811720730079795819)
  ·
    refine ⟨81596749217581095119693729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54397832811720730079795819 81596749217581095119693729)
    ·
      refine ⟨61197561913185821339770297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81596749217581095119693729 61197561913185821339770297)
      ·
        refine ⟨45898171434889366004827723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61197561913185821339770297 45898171434889366004827723)
        ·
          refine ⟨68847257152334049007241585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45898171434889366004827723 68847257152334049007241585)
          ·
            refine ⟨51635442864250536755431189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68847257152334049007241585 51635442864250536755431189)
            ·
              refine ⟨2420411384261743910410837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 51635442864250536755431189 2420411384261743910410837)
              ·
                refine ⟨28364195909317311450127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2420411384261743910410837 28364195909317311450127)
                ·
                  rfl

theorem cell23_1491455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 8].length) (baseStart_1491455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1491455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1491455 prefixEnd_1491455 := by exact prefixLift 1491455
  have htrace : WordTrace (prefixWord ++ tailWord_1491455) baseStart_1491455 baseEnd_1491455 := by
    simpa [prefixWord, tailWord_1491455, baseEnd_1491455] using wordTrace_append hprefix tailTrace_1491455
  have hstable : (prefixWord ++ tailWord_1491455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491455).length < 2 ^ (prefixWord ++ tailWord_1491455).sum := by decide
  have hdescent : baseEnd_1491455 < baseStart_1491455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491482 : List Nat := [3, 1, 1, 3, 1, 1, 3, 1, 3, 3, 3]
def baseStart_1491482 : Nat := 118140960795 + 1491482 * 2 ^ 59
def prefixEnd_1491482 : Nat := 4983230072969 + 3 ^ 40 * 1491482 * 2
def baseEnd_1491482 : Nat := 765847153529238803515805

theorem tailTrace_1491482 : CollatzResearch.WordTrace tailWord_1491482 prefixEnd_1491482 765847153529238803515805 := by
  unfold tailWord_1491482
  simp only [CollatzResearch.WordTrace]
  refine ⟨13599704395655728422757175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36265878388415275794019133 13599704395655728422757175)
  ·
    refine ⟨20399556593483592634135763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13599704395655728422757175 20399556593483592634135763)
    ·
      refine ⟨30599334890225388951203645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20399556593483592634135763 30599334890225388951203645)
      ·
        refine ⟨11474750583834520856701367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30599334890225388951203645 11474750583834520856701367)
        ·
          refine ⟨17212125875751781285052051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11474750583834520856701367 17212125875751781285052051)
          ·
            refine ⟨25818188813627671927578077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17212125875751781285052051 25818188813627671927578077)
            ·
              refine ⟨9681820805110376972841779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25818188813627671927578077 9681820805110376972841779)
              ·
                refine ⟨14522731207665565459262669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9681820805110376972841779 14522731207665565459262669)
                ·
                  refine ⟨5446024202874587047223501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14522731207665565459262669 5446024202874587047223501)
                  ·
                    refine ⟨2042259076077970142708813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5446024202874587047223501 2042259076077970142708813)
                    ·
                      refine ⟨765847153529238803515805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2042259076077970142708813 765847153529238803515805)
                      ·
                        rfl

theorem cell23_1491482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 3, 3, 3].length) (baseStart_1491482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1491482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1491482 prefixEnd_1491482 := by exact prefixLift 1491482
  have htrace : WordTrace (prefixWord ++ tailWord_1491482) baseStart_1491482 baseEnd_1491482 := by
    simpa [prefixWord, tailWord_1491482, baseEnd_1491482] using wordTrace_append hprefix tailTrace_1491482
  have hstable : (prefixWord ++ tailWord_1491482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491482).length < 2 ^ (prefixWord ++ tailWord_1491482).sum := by decide
  have hdescent : baseEnd_1491482 < baseStart_1491482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491509 : List Nat := [1, 3, 3, 1, 1, 2, 1, 1, 5, 3, 2]
def baseStart_1491509 : Nat := 118140960795 + 1491509 * 2 ^ 59
def prefixEnd_1491509 : Nat := 4983230072969 + 3 ^ 40 * 1491509 * 2
def baseEnd_1491509 : Nat := 765861017506910197878181

theorem tailTrace_1491509 : CollatzResearch.WordTrace tailWord_1491509 prefixEnd_1491509 765861017506910197878181 := by
  unfold tailWord_1491509
  simp only [CollatzResearch.WordTrace]
  refine ⟨54399802353525097302261581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36266534902350064868174387 54399802353525097302261581)
  ·
    refine ⟨20399925882571911488348093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54399802353525097302261581 20399925882571911488348093)
    ·
      refine ⟨7649972205964466808130535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20399925882571911488348093 7649972205964466808130535)
      ·
        refine ⟨11474958308946700212195803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7649972205964466808130535 11474958308946700212195803)
        ·
          refine ⟨17212437463420050318293705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11474958308946700212195803 17212437463420050318293705)
          ·
            refine ⟨12909328097565037738720279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17212437463420050318293705 12909328097565037738720279)
            ·
              refine ⟨19363992146347556608080419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12909328097565037738720279 19363992146347556608080419)
              ·
                refine ⟨29045988219521334912120629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19363992146347556608080419 29045988219521334912120629)
                ·
                  refine ⟨2723061395580125148011309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29045988219521334912120629 2723061395580125148011309)
                  ·
                    refine ⟨1021148023342546930504241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2723061395580125148011309 1021148023342546930504241)
                    ·
                      refine ⟨765861017506910197878181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1021148023342546930504241 765861017506910197878181)
                      ·
                        rfl

theorem cell23_1491509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 5, 3, 2].length) (baseStart_1491509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1491509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1491509 prefixEnd_1491509 := by exact prefixLift 1491509
  have htrace : WordTrace (prefixWord ++ tailWord_1491509) baseStart_1491509 baseEnd_1491509 := by
    simpa [prefixWord, tailWord_1491509, baseEnd_1491509] using wordTrace_append hprefix tailTrace_1491509
  have hstable : (prefixWord ++ tailWord_1491509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491509).length < 2 ^ (prefixWord ++ tailWord_1491509).sum := by decide
  have hdescent : baseEnd_1491509 < baseStart_1491509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491516 : List Nat := [2, 2, 2, 2, 3, 1, 2, 3, 2, 1, 3]
def baseStart_1491516 : Nat := 118140960795 + 1491516 * 2 ^ 59
def prefixEnd_1491516 : Nat := 4983230072969 + 3 ^ 40 * 1491516 * 2
def baseEnd_1491516 : Nat := 765864611871491670490649

theorem tailTrace_1491516 : CollatzResearch.WordTrace tailWord_1491516 prefixEnd_1491516 765864611871491670490649 := by
  unfold tailWord_1491516
  simp only [CollatzResearch.WordTrace]
  refine ⟨27200028832249868748883201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36266705109666491665177601 27200028832249868748883201)
  ·
    refine ⟨20400021624187401561662401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27200028832249868748883201 20400021624187401561662401)
    ·
      refine ⟨15300016218140551171246801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20400021624187401561662401 15300016218140551171246801)
      ·
        refine ⟨11475012163605413378435101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15300016218140551171246801 11475012163605413378435101)
        ·
          refine ⟨4303129561352030016913163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11475012163605413378435101 4303129561352030016913163)
          ·
            refine ⟨6454694342028045025369745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4303129561352030016913163 6454694342028045025369745)
            ·
              refine ⟨4841020756521033769027309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6454694342028045025369745 4841020756521033769027309)
              ·
                refine ⟨1815382783695387663385241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4841020756521033769027309 1815382783695387663385241)
                ·
                  refine ⟨1361537087771540747538931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1815382783695387663385241 1361537087771540747538931)
                  ·
                    refine ⟨2042305631657311121308397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1361537087771540747538931 2042305631657311121308397)
                    ·
                      refine ⟨765864611871491670490649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2042305631657311121308397 765864611871491670490649)
                      ·
                        rfl

theorem cell23_1491516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 3, 2, 1, 3].length) (baseStart_1491516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1491516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1491516 prefixEnd_1491516 := by exact prefixLift 1491516
  have htrace : WordTrace (prefixWord ++ tailWord_1491516) baseStart_1491516 baseEnd_1491516 := by
    simpa [prefixWord, tailWord_1491516, baseEnd_1491516] using wordTrace_append hprefix tailTrace_1491516
  have hstable : (prefixWord ++ tailWord_1491516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491516).length < 2 ^ (prefixWord ++ tailWord_1491516).sum := by decide
  have hdescent : baseEnd_1491516 < baseStart_1491516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491552 : List Nat := [2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 4]
def baseStart_1491552 : Nat := 118140960795 + 1491552 * 2 ^ 59
def prefixEnd_1491552 : Nat := 4983230072969 + 3 ^ 40 * 1491552 * 2
def baseEnd_1491552 : Nat := 765883097175053529640483

theorem tailTrace_1491552 : CollatzResearch.WordTrace tailWord_1491552 prefixEnd_1491552 765883097175053529640483 := by
  unfold tailWord_1491552
  simp only [CollatzResearch.WordTrace]
  refine ⟨27200685346184657823038455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36267580461579543764051273 27200685346184657823038455)
  ·
    refine ⟨40801028019276986734557683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27200685346184657823038455 40801028019276986734557683)
    ·
      refine ⟨61201542028915480101836525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40801028019276986734557683 61201542028915480101836525)
      ·
        refine ⟨22950578260843305038188697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61201542028915480101836525 22950578260843305038188697)
        ·
          refine ⟨17212933695632478778641523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22950578260843305038188697 17212933695632478778641523)
          ·
            refine ⟨25819400543448718167962285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17212933695632478778641523 25819400543448718167962285)
            ·
              refine ⟨9682275203793269312985857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25819400543448718167962285 9682275203793269312985857)
              ·
                refine ⟨7261706402844951984739393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9682275203793269312985857 7261706402844951984739393)
                ·
                  refine ⟨5446279802133713988554545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7261706402844951984739393 5446279802133713988554545)
                  ·
                    refine ⟨4084709851600285491415909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5446279802133713988554545 4084709851600285491415909)
                    ·
                      refine ⟨765883097175053529640483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4084709851600285491415909 765883097175053529640483)
                      ·
                        rfl

theorem cell23_1491552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 4].length) (baseStart_1491552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1491552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1491552 prefixEnd_1491552 := by exact prefixLift 1491552
  have htrace : WordTrace (prefixWord ++ tailWord_1491552) baseStart_1491552 baseEnd_1491552 := by
    simpa [prefixWord, tailWord_1491552, baseEnd_1491552] using wordTrace_append hprefix tailTrace_1491552
  have hstable : (prefixWord ++ tailWord_1491552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491552).length < 2 ^ (prefixWord ++ tailWord_1491552).sum := by decide
  have hdescent : baseEnd_1491552 < baseStart_1491552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491556 : List Nat := [2, 3, 1, 1, 2, 2, 3, 1, 4, 2, 2]
def baseStart_1491556 : Nat := 118140960795 + 1491556 * 2 ^ 59
def prefixEnd_1491556 : Nat := 4983230072969 + 3 ^ 40 * 1491556 * 2
def baseEnd_1491556 : Nat := 765885151097671513990465

theorem tailTrace_1491556 : CollatzResearch.WordTrace tailWord_1491556 prefixEnd_1491556 765885151097671513990465 := by
  unfold tailWord_1491556
  simp only [CollatzResearch.WordTrace]
  refine ⟨27200758292177412164611261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36267677722903216219481681 27200758292177412164611261)
  ·
    refine ⟨10200284359566529561729223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27200758292177412164611261 10200284359566529561729223)
    ·
      refine ⟨15300426539349794342593835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10200284359566529561729223 15300426539349794342593835)
      ·
        refine ⟨22950639809024691513890753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15300426539349794342593835 22950639809024691513890753)
        ·
          refine ⟨17212979856768518635418065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22950639809024691513890753 17212979856768518635418065)
          ·
            refine ⟨12909734892576388976563549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17212979856768518635418065 12909734892576388976563549)
            ·
              refine ⟨4841150584716145866211331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12909734892576388976563549 4841150584716145866211331)
              ·
                refine ⟨7261725877074218799316997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4841150584716145866211331 7261725877074218799316997)
                ·
                  refine ⟨1361573601951416024871937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7261725877074218799316997 1361573601951416024871937)
                  ·
                    refine ⟨1021180201463562018653953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1361573601951416024871937 1021180201463562018653953)
                    ·
                      refine ⟨765885151097671513990465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1021180201463562018653953 765885151097671513990465)
                      ·
                        rfl

theorem cell23_1491556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 4, 2, 2].length) (baseStart_1491556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1491556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1491556 prefixEnd_1491556 := by exact prefixLift 1491556
  have htrace : WordTrace (prefixWord ++ tailWord_1491556) baseStart_1491556 baseEnd_1491556 := by
    simpa [prefixWord, tailWord_1491556, baseEnd_1491556] using wordTrace_append hprefix tailTrace_1491556
  have hstable : (prefixWord ++ tailWord_1491556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491556).length < 2 ^ (prefixWord ++ tailWord_1491556).sum := by decide
  have hdescent : baseEnd_1491556 < baseStart_1491556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491646 : List Nat := [4, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4]
def baseStart_1491646 : Nat := 118140960795 + 1491646 * 2 ^ 59
def prefixEnd_1491646 : Nat := 4983230072969 + 3 ^ 40 * 1491646 * 2
def baseEnd_1491646 : Nat := 765931364356576161865051

theorem tailTrace_1491646 : CollatzResearch.WordTrace tailWord_1491646 prefixEnd_1491646 765931364356576161865051 := by
  unfold tailWord_1491646
  simp only [CollatzResearch.WordTrace]
  refine ⟨6800599894253596212499849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36269866102685846466665861 6800599894253596212499849)
  ·
    refine ⟨5100449920690197159374887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6800599894253596212499849 5100449920690197159374887)
    ·
      refine ⟨7650674881035295739062331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5100449920690197159374887 7650674881035295739062331)
      ·
        refine ⟨11476012321552943608593497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7650674881035295739062331 11476012321552943608593497)
        ·
          refine ⟨8607009241164707706445123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11476012321552943608593497 8607009241164707706445123)
          ·
            refine ⟨12910513861747061559667685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8607009241164707706445123 12910513861747061559667685)
            ·
              refine ⟨2420721349077574042437691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12910513861747061559667685 2420721349077574042437691)
              ·
                refine ⟨3631082023616361063656537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2420721349077574042437691 3631082023616361063656537)
                ·
                  refine ⟨2723311517712270797742403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3631082023616361063656537 2723311517712270797742403)
                  ·
                    refine ⟨4084967276568406196613605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2723311517712270797742403 4084967276568406196613605)
                    ·
                      refine ⟨765931364356576161865051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4084967276568406196613605 765931364356576161865051)
                      ·
                        rfl

theorem cell23_1491646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4].length) (baseStart_1491646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1491646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1491646 prefixEnd_1491646 := by exact prefixLift 1491646
  have htrace : WordTrace (prefixWord ++ tailWord_1491646) baseStart_1491646 baseEnd_1491646 := by
    simpa [prefixWord, tailWord_1491646, baseEnd_1491646] using wordTrace_append hprefix tailTrace_1491646
  have hstable : (prefixWord ++ tailWord_1491646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491646).length < 2 ^ (prefixWord ++ tailWord_1491646).sum := by decide
  have hdescent : baseEnd_1491646 < baseStart_1491646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491692 : List Nat := [2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 7]
def baseStart_1491692 : Nat := 118140960795 + 1491692 * 2 ^ 59
def prefixEnd_1491692 : Nat := 4983230072969 + 3 ^ 40 * 1491692 * 2
def baseEnd_1491692 : Nat := 765954984466682981889839

theorem tailTrace_1491692 : CollatzResearch.WordTrace tailWord_1491692 prefixEnd_1491692 765954984466682981889839 := by
  unfold tailWord_1491692
  simp only [CollatzResearch.WordTrace]
  refine ⟨27203238455931059778086665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36270984607908079704115553 27203238455931059778086665)
  ·
    refine ⟨20402428841948294833564999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27203238455931059778086665 20402428841948294833564999)
    ·
      refine ⟨30603643262922442250347499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20402428841948294833564999 30603643262922442250347499)
      ·
        refine ⟨45905464894383663375521249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30603643262922442250347499 45905464894383663375521249)
        ·
          refine ⟨34429098670787747531640937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45905464894383663375521249 34429098670787747531640937)
          ·
            refine ⟨25821824003090810648730703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34429098670787747531640937 25821824003090810648730703)
            ·
              refine ⟨38732736004636215973096055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25821824003090810648730703 38732736004636215973096055)
              ·
                refine ⟨58099104006954323959644083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38732736004636215973096055 58099104006954323959644083)
                ·
                  refine ⟨87148656010431485939466125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58099104006954323959644083 87148656010431485939466125)
                  ·
                    refine ⟨32680746003911807227299797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 87148656010431485939466125 32680746003911807227299797)
                    ·
                      refine ⟨765954984466682981889839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 32680746003911807227299797 765954984466682981889839)
                      ·
                        rfl

theorem cell23_1491692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 7].length) (baseStart_1491692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1491692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1491692 prefixEnd_1491692 := by exact prefixLift 1491692
  have htrace : WordTrace (prefixWord ++ tailWord_1491692) baseStart_1491692 baseEnd_1491692 := by
    simpa [prefixWord, tailWord_1491692, baseEnd_1491692] using wordTrace_append hprefix tailTrace_1491692
  have hstable : (prefixWord ++ tailWord_1491692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491692).length < 2 ^ (prefixWord ++ tailWord_1491692).sum := by decide
  have hdescent : baseEnd_1491692 < baseStart_1491692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491696 : List Nat := [2, 1, 1, 1, 3, 1, 5, 2, 3, 1, 3]
def baseStart_1491696 : Nat := 118140960795 + 1491696 * 2 ^ 59
def prefixEnd_1491696 : Nat := 4983230072969 + 3 ^ 40 * 1491696 * 2
def baseEnd_1491696 : Nat := 765957038389300966239821

theorem tailTrace_1491696 : CollatzResearch.WordTrace tailWord_1491696 prefixEnd_1491696 765957038389300966239821 := by
  unfold tailWord_1491696
  simp only [CollatzResearch.WordTrace]
  refine ⟨27203311401923814119659471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36271081869231752159545961 27203311401923814119659471)
  ·
    refine ⟨40804967102885721179489207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27203311401923814119659471 40804967102885721179489207)
    ·
      refine ⟨61207450654328581769233811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40804967102885721179489207 61207450654328581769233811)
      ·
        refine ⟨91811175981492872653850717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61207450654328581769233811 91811175981492872653850717)
        ·
          refine ⟨34429190993059827245194019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91811175981492872653850717 34429190993059827245194019)
          ·
            refine ⟨51643786489589740867791029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34429190993059827245194019 51643786489589740867791029)
            ·
              refine ⟨4841604983399038206355409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51643786489589740867791029 4841604983399038206355409)
              ·
                refine ⟨3631203737549278654766557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4841604983399038206355409 3631203737549278654766557)
                ·
                  refine ⟨1361701401580979495537459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3631203737549278654766557 1361701401580979495537459)
                  ·
                    refine ⟨2042552102371469243306189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1361701401580979495537459 2042552102371469243306189)
                    ·
                      refine ⟨765957038389300966239821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2042552102371469243306189 765957038389300966239821)
                      ·
                        rfl

theorem cell23_1491696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 2, 3, 1, 3].length) (baseStart_1491696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1491696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1491696 prefixEnd_1491696 := by exact prefixLift 1491696
  have htrace : WordTrace (prefixWord ++ tailWord_1491696) baseStart_1491696 baseEnd_1491696 := by
    simpa [prefixWord, tailWord_1491696, baseEnd_1491696] using wordTrace_append hprefix tailTrace_1491696
  have hstable : (prefixWord ++ tailWord_1491696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491696).length < 2 ^ (prefixWord ++ tailWord_1491696).sum := by decide
  have hdescent : baseEnd_1491696 < baseStart_1491696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491699 : List Nat := [1, 1, 1, 2, 2, 3, 1, 6, 1, 5]
def baseStart_1491699 : Nat := 118140960795 + 1491699 * 2 ^ 59
def prefixEnd_1491699 : Nat := 4983230072969 + 3 ^ 40 * 1491699 * 2
def baseEnd_1491699 : Nat := 255319526277088151500769

theorem tailTrace_1491699 : CollatzResearch.WordTrace tailWord_1491699 prefixEnd_1491699 255319526277088151500769 := by
  unfold tailWord_1491699
  simp only [CollatzResearch.WordTrace]
  refine ⟨54406732222836759751678151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36271154815224506501118767 54406732222836759751678151)
  ·
    refine ⟨81610098334255139627517227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54406732222836759751678151 81610098334255139627517227)
    ·
      refine ⟨122415147501382709441275841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81610098334255139627517227 122415147501382709441275841)
      ·
        refine ⟨91811360626037032080956881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122415147501382709441275841 91811360626037032080956881)
        ·
          refine ⟨68858520469527774060717661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91811360626037032080956881 68858520469527774060717661)
          ·
            refine ⟨25821945176072915272769123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68858520469527774060717661 25821945176072915272769123)
            ·
              refine ⟨38732917764109372909153685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25821945176072915272769123 38732917764109372909153685)
              ·
                refine ⟨1815605520192626855116579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 38732917764109372909153685 1815605520192626855116579)
                ·
                  refine ⟨2723408280288940282674869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1815605520192626855116579 2723408280288940282674869)
                  ·
                    refine ⟨255319526277088151500769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2723408280288940282674869 255319526277088151500769)
                    ·
                      rfl

theorem cell23_1491699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 6, 1, 5].length) (baseStart_1491699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1491699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1491699 prefixEnd_1491699 := by exact prefixLift 1491699
  have htrace : WordTrace (prefixWord ++ tailWord_1491699) baseStart_1491699 baseEnd_1491699 := by
    simpa [prefixWord, tailWord_1491699, baseEnd_1491699] using wordTrace_append hprefix tailTrace_1491699
  have hstable : (prefixWord ++ tailWord_1491699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491699).length < 2 ^ (prefixWord ++ tailWord_1491699).sum := by decide
  have hdescent : baseEnd_1491699 < baseStart_1491699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491700 : List Nat := [2, 6, 1, 1, 2, 1, 1, 1, 1, 4, 3]
def baseStart_1491700 : Nat := 118140960795 + 1491700 * 2 ^ 59
def prefixEnd_1491700 : Nat := 4983230072969 + 3 ^ 40 * 1491700 * 2
def baseEnd_1491700 : Nat := 765959092311918950589803

theorem tailTrace_1491700 : CollatzResearch.WordTrace tailWord_1491700 prefixEnd_1491700 765959092311918950589803 := by
  unfold tailWord_1491700
  simp only [CollatzResearch.WordTrace]
  refine ⟨27203384347916568461232277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36271179130555424614976369 27203384347916568461232277)
  ·
    refine ⟨1275158641308589146620263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 27203384347916568461232277 1275158641308589146620263)
    ·
      refine ⟨1912737961962883719930395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1275158641308589146620263 1912737961962883719930395)
      ·
        refine ⟨2869106942944325579895593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1912737961962883719930395 2869106942944325579895593)
        ·
          refine ⟨2151830207208244184921695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2869106942944325579895593 2151830207208244184921695)
          ·
            refine ⟨3227745310812366277382543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2151830207208244184921695 3227745310812366277382543)
            ·
              refine ⟨4841617966218549416073815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3227745310812366277382543 4841617966218549416073815)
              ·
                refine ⟨7262426949327824124110723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4841617966218549416073815 7262426949327824124110723)
                ·
                  refine ⟨10893640423991736186166085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7262426949327824124110723 10893640423991736186166085)
                  ·
                    refine ⟨2042557579498450534906141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10893640423991736186166085 2042557579498450534906141)
                    ·
                      refine ⟨765959092311918950589803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2042557579498450534906141 765959092311918950589803)
                      ·
                        rfl

theorem cell23_1491700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_1491700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1491700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1491700 prefixEnd_1491700 := by exact prefixLift 1491700
  have htrace : WordTrace (prefixWord ++ tailWord_1491700) baseStart_1491700 baseEnd_1491700 := by
    simpa [prefixWord, tailWord_1491700, baseEnd_1491700] using wordTrace_append hprefix tailTrace_1491700
  have hstable : (prefixWord ++ tailWord_1491700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491700).length < 2 ^ (prefixWord ++ tailWord_1491700).sum := by decide
  have hdescent : baseEnd_1491700 < baseStart_1491700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491716 : List Nat := [2, 3, 2, 2, 1, 1, 3, 3, 1, 5]
def baseStart_1491716 : Nat := 118140960795 + 1491716 * 2 ^ 59
def prefixEnd_1491716 : Nat := 4983230072969 + 3 ^ 40 * 1491716 * 2
def baseEnd_1491716 : Nat := 255322436000796962663243

theorem tailTrace_1491716 : CollatzResearch.WordTrace tailWord_1491716 prefixEnd_1491716 255322436000796962663243 := by
  unfold tailWord_1491716
  simp only [CollatzResearch.WordTrace]
  refine ⟨27203676131887585827523501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36271568175850114436698001 27203676131887585827523501)
  ·
    refine ⟨10201378549457844685321313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27203676131887585827523501 10201378549457844685321313)
    ·
      refine ⟨7651033912093383513990985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10201378549457844685321313 7651033912093383513990985)
      ·
        refine ⟨5738275434070037635493239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7651033912093383513990985 5738275434070037635493239)
        ·
          refine ⟨8607413151105056453239859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5738275434070037635493239 8607413151105056453239859)
          ·
            refine ⟨12911119726657584679859789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8607413151105056453239859 12911119726657584679859789)
            ·
              refine ⟨4841669897496594254947421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12911119726657584679859789 4841669897496594254947421)
              ·
                refine ⟨1815626211561222845605283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4841669897496594254947421 1815626211561222845605283)
                ·
                  refine ⟨2723439317341834268407925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1815626211561222845605283 2723439317341834268407925)
                  ·
                    refine ⟨255322436000796962663243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2723439317341834268407925 255322436000796962663243)
                    ·
                      rfl

theorem cell23_1491716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 3, 1, 5].length) (baseStart_1491716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1491716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1491716 prefixEnd_1491716 := by exact prefixLift 1491716
  have htrace : WordTrace (prefixWord ++ tailWord_1491716) baseStart_1491716 baseEnd_1491716 := by
    simpa [prefixWord, tailWord_1491716, baseEnd_1491716] using wordTrace_append hprefix tailTrace_1491716
  have hstable : (prefixWord ++ tailWord_1491716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491716).length < 2 ^ (prefixWord ++ tailWord_1491716).sum := by decide
  have hdescent : baseEnd_1491716 < baseStart_1491716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491746 : List Nat := [3, 3, 1, 1, 2, 2, 3, 1, 1, 6]
def baseStart_1491746 : Nat := 118140960795 + 1491746 * 2 ^ 59
def prefixEnd_1491746 : Nat := 4983230072969 + 3 ^ 40 * 1491746 * 2
def baseEnd_1491746 : Nat := 255327570807341923538197

theorem tailTrace_1491746 : CollatzResearch.WordTrace tailWord_1491746 prefixEnd_1491746 255327570807341923538197 := by
  unfold tailWord_1491746
  simp only [CollatzResearch.WordTrace]
  refine ⟨13602111613416621694659773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36272297635777657852426061 13602111613416621694659773)
  ·
    refine ⟨5100791855031233135497415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13602111613416621694659773 5100791855031233135497415)
    ·
      refine ⟨7651187782546849703246123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5100791855031233135497415 7651187782546849703246123)
      ·
        refine ⟨11476781673820274554869185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7651187782546849703246123 11476781673820274554869185)
        ·
          refine ⟨8607586255365205916151889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11476781673820274554869185 8607586255365205916151889)
          ·
            refine ⟨6455689691523904437113917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8607586255365205916151889 6455689691523904437113917)
            ·
              refine ⟨2420883634321464163917719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6455689691523904437113917 2420883634321464163917719)
              ·
                refine ⟨3631325451482196245876579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2420883634321464163917719 3631325451482196245876579)
                ·
                  refine ⟨5446988177223294368814869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3631325451482196245876579 5446988177223294368814869)
                  ·
                    refine ⟨255327570807341923538197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5446988177223294368814869 255327570807341923538197)
                    ·
                      rfl

theorem cell23_1491746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 1, 1, 6].length) (baseStart_1491746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1491746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1491746 prefixEnd_1491746 := by exact prefixLift 1491746
  have htrace : WordTrace (prefixWord ++ tailWord_1491746) baseStart_1491746 baseEnd_1491746 := by
    simpa [prefixWord, tailWord_1491746, baseEnd_1491746] using wordTrace_append hprefix tailTrace_1491746
  have hstable : (prefixWord ++ tailWord_1491746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491746).length < 2 ^ (prefixWord ++ tailWord_1491746).sum := by decide
  have hdescent : baseEnd_1491746 < baseStart_1491746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491749 : List Nat := [1, 3, 1, 2, 3, 1, 3, 1, 1, 1, 6]
def baseStart_1491749 : Nat := 118140960795 + 1491749 * 2 ^ 59
def prefixEnd_1491749 : Nat := 4983230072969 + 3 ^ 40 * 1491749 * 2
def baseEnd_1491749 : Nat := 765984252863989258877077

theorem tailTrace_1491749 : CollatzResearch.WordTrace tailWord_1491749 prefixEnd_1491749 765984252863989258877077 := by
  unfold tailWord_1491749
  simp only [CollatzResearch.WordTrace]
  refine ⟨54408555872655618290998301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36272370581770412193998867 54408555872655618290998301)
  ·
    refine ⟨20403208452245856859124363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54408555872655618290998301 20403208452245856859124363)
    ·
      refine ⟨30604812678368785288686545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20403208452245856859124363 30604812678368785288686545)
      ·
        refine ⟨22953609508776588966514909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30604812678368785288686545 22953609508776588966514909)
        ·
          refine ⟨8607603565791220862443091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22953609508776588966514909 8607603565791220862443091)
          ·
            refine ⟨12911405348686831293664637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8607603565791220862443091 12911405348686831293664637)
            ·
              refine ⟨4841777005757561735124239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12911405348686831293664637 4841777005757561735124239)
              ·
                refine ⟨7262665508636342602686359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4841777005757561735124239 7262665508636342602686359)
                ·
                  refine ⟨10893998262954513904029539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7262665508636342602686359 10893998262954513904029539)
                  ·
                    refine ⟨16340997394431770856044309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10893998262954513904029539 16340997394431770856044309)
                    ·
                      refine ⟨765984252863989258877077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16340997394431770856044309 765984252863989258877077)
                      ·
                        rfl

theorem cell23_1491749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 1, 6].length) (baseStart_1491749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1491749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1491749 prefixEnd_1491749 := by exact prefixLift 1491749
  have htrace : WordTrace (prefixWord ++ tailWord_1491749) baseStart_1491749 baseEnd_1491749 := by
    simpa [prefixWord, tailWord_1491749, baseEnd_1491749] using wordTrace_append hprefix tailTrace_1491749
  have hstable : (prefixWord ++ tailWord_1491749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491749).length < 2 ^ (prefixWord ++ tailWord_1491749).sum := by decide
  have hdescent : baseEnd_1491749 < baseStart_1491749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491764 : List Nat := [2, 5, 1, 1, 3, 2, 1, 3, 1, 1, 3]
def baseStart_1491764 : Nat := 118140960795 + 1491764 * 2 ^ 59
def prefixEnd_1491764 : Nat := 4983230072969 + 3 ^ 40 * 1491764 * 2
def baseEnd_1491764 : Nat := 765991955073806700189509

theorem tailTrace_1491764 : CollatzResearch.WordTrace tailWord_1491764 prefixEnd_1491764 765991955073806700189509 := by
  unfold tailWord_1491764
  simp only [CollatzResearch.WordTrace]
  refine ⟨27204551483800637926397173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36272735311734183901862897 27204551483800637926397173)
  ·
    refine ⟨2550426701606309805599735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27204551483800637926397173 2550426701606309805599735)
    ·
      refine ⟨3825640052409464708399603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2550426701606309805599735 3825640052409464708399603)
      ·
        refine ⟨5738460078614197062599405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3825640052409464708399603 5738460078614197062599405)
        ·
          refine ⟨2151922529480323898474777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5738460078614197062599405 2151922529480323898474777)
          ·
            refine ⟨1613941897110242923856083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2151922529480323898474777 1613941897110242923856083)
            ·
              refine ⟨2420912845665364385784125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1613941897110242923856083 2420912845665364385784125)
              ·
                refine ⟨907842317124511644669047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2420912845665364385784125 907842317124511644669047)
                ·
                  refine ⟨1361763475686767467003571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 907842317124511644669047 1361763475686767467003571)
                  ·
                    refine ⟨2042645213530151200505357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1361763475686767467003571 2042645213530151200505357)
                    ·
                      refine ⟨765991955073806700189509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2042645213530151200505357 765991955073806700189509)
                      ·
                        rfl

theorem cell23_1491764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 3, 1, 1, 3].length) (baseStart_1491764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1491764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1491764 prefixEnd_1491764 := by exact prefixLift 1491764
  have htrace : WordTrace (prefixWord ++ tailWord_1491764) baseStart_1491764 baseEnd_1491764 := by
    simpa [prefixWord, tailWord_1491764, baseEnd_1491764] using wordTrace_append hprefix tailTrace_1491764
  have hstable : (prefixWord ++ tailWord_1491764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491764).length < 2 ^ (prefixWord ++ tailWord_1491764).sum := by decide
  have hdescent : baseEnd_1491764 < baseStart_1491764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491773 : List Nat := [1, 4, 1, 4, 2, 1, 2, 1, 1, 1, 5]
def baseStart_1491773 : Nat := 118140960795 + 1491773 * 2 ^ 59
def prefixEnd_1491773 : Nat := 4983230072969 + 3 ^ 40 * 1491773 * 2
def baseEnd_1491773 : Nat := 765996576399697164976967

theorem tailTrace_1491773 : CollatzResearch.WordTrace tailWord_1491773 prefixEnd_1491773 765996576399697164976967 := by
  unfold tailWord_1491773
  simp only [CollatzResearch.WordTrace]
  refine ⟨54409431224568670389871973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36272954149712446926581315 54409431224568670389871973)
  ·
    refine ⟨10201768354606625698100995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54409431224568670389871973 10201768354606625698100995)
    ·
      refine ⟨15302652531909938547151493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10201768354606625698100995 15302652531909938547151493)
      ·
        refine ⟨2869247349733113477590905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15302652531909938547151493 2869247349733113477590905)
        ·
          refine ⟨2151935512299835108193179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2869247349733113477590905 2151935512299835108193179)
          ·
            refine ⟨3227903268449752662289769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2151935512299835108193179 3227903268449752662289769)
            ·
              refine ⟨2420927451337314496717327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3227903268449752662289769 2420927451337314496717327)
              ·
                refine ⟨3631391177005971745075991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2420927451337314496717327 3631391177005971745075991)
                ·
                  refine ⟨5447086765508957617613987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3631391177005971745075991 5447086765508957617613987)
                  ·
                    refine ⟨8170630148263436426420981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5447086765508957617613987 8170630148263436426420981)
                    ·
                      refine ⟨765996576399697164976967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8170630148263436426420981 765996576399697164976967)
                      ·
                        rfl

theorem cell23_1491773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_1491773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1491773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1491773 prefixEnd_1491773 := by exact prefixLift 1491773
  have htrace : WordTrace (prefixWord ++ tailWord_1491773) baseStart_1491773 baseEnd_1491773 := by
    simpa [prefixWord, tailWord_1491773, baseEnd_1491773] using wordTrace_append hprefix tailTrace_1491773
  have hstable : (prefixWord ++ tailWord_1491773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491773).length < 2 ^ (prefixWord ++ tailWord_1491773).sum := by decide
  have hdescent : baseEnd_1491773 < baseStart_1491773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491809 : List Nat := [1, 2, 3, 1, 1, 1, 2, 1, 4, 3, 4]
def baseStart_1491809 : Nat := 118140960795 + 1491809 * 2 ^ 59
def prefixEnd_1491809 : Nat := 4983230072969 + 3 ^ 40 * 1491809 * 2
def baseEnd_1491809 : Nat := 766015061703259024126801

theorem tailTrace_1491809 : CollatzResearch.WordTrace tailWord_1491809 prefixEnd_1491809 766015061703259024126801 := by
  unfold tailWord_1491809
  simp only [CollatzResearch.WordTrace]
  refine ⟨54410744252438248538182481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36273829501625499025454987 54410744252438248538182481)
  ·
    refine ⟨40808058189328686403636861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54410744252438248538182481 40808058189328686403636861)
    ·
      refine ⟨15303021820998257401363823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40808058189328686403636861 15303021820998257401363823)
      ·
        refine ⟨22954532731497386102045735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15303021820998257401363823 22954532731497386102045735)
        ·
          refine ⟨34431799097246079153068603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22954532731497386102045735 34431799097246079153068603)
          ·
            refine ⟨51647698645869118729602905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34431799097246079153068603 51647698645869118729602905)
            ·
              refine ⟨38735773984401839047202179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51647698645869118729602905 38735773984401839047202179)
              ·
                refine ⟨58103660976602758570803269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38735773984401839047202179 58103660976602758570803269)
                ·
                  refine ⟨10894436433113017232025613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58103660976602758570803269 10894436433113017232025613)
                  ·
                    refine ⟨4085413662417381462009605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10894436433113017232025613 4085413662417381462009605)
                    ·
                      refine ⟨766015061703259024126801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4085413662417381462009605 766015061703259024126801)
                      ·
                        rfl

theorem cell23_1491809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 3, 4].length) (baseStart_1491809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1491809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1491809 prefixEnd_1491809 := by exact prefixLift 1491809
  have htrace : WordTrace (prefixWord ++ tailWord_1491809) baseStart_1491809 baseEnd_1491809 := by
    simpa [prefixWord, tailWord_1491809, baseEnd_1491809] using wordTrace_append hprefix tailTrace_1491809
  have hstable : (prefixWord ++ tailWord_1491809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491809).length < 2 ^ (prefixWord ++ tailWord_1491809).sum := by decide
  have hdescent : baseEnd_1491809 < baseStart_1491809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491838 : List Nat := [4, 2, 3, 1, 2, 2, 2, 2, 1, 2, 2]
def baseStart_1491838 : Nat := 118140960795 + 1491838 * 2 ^ 59
def prefixEnd_1491838 : Nat := 4983230072969 + 3 ^ 40 * 1491838 * 2
def baseEnd_1491838 : Nat := 766029952642239410664169

theorem tailTrace_1491838 : CollatzResearch.WordTrace tailWord_1491838 prefixEnd_1491838 766029952642239410664169 := by
  unfold tailWord_1491838
  simp only [CollatzResearch.WordTrace]
  refine ⟨6801475246166648311373521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36274534646222124327325445 6801475246166648311373521)
  ·
    refine ⟨5101106434624986233530141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6801475246166648311373521 5101106434624986233530141)
    ·
      refine ⟨1912914912984369837573803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5101106434624986233530141 1912914912984369837573803)
      ·
        refine ⟨2869372369476554756360705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1912914912984369837573803 2869372369476554756360705)
        ·
          refine ⟨2152029277107416067270529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2869372369476554756360705 2152029277107416067270529)
          ·
            refine ⟨1614021957830562050452897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2152029277107416067270529 1614021957830562050452897)
            ·
              refine ⟨1210516468372921537839673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1614021957830562050452897 1210516468372921537839673)
              ·
                refine ⟨907887351279691153379755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1210516468372921537839673 907887351279691153379755)
                ·
                  refine ⟨1361831026919536730069633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 907887351279691153379755 1361831026919536730069633)
                  ·
                    refine ⟨1021373270189652547552225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1361831026919536730069633 1021373270189652547552225)
                    ·
                      refine ⟨766029952642239410664169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1021373270189652547552225 766029952642239410664169)
                      ·
                        rfl

theorem cell23_1491838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_1491838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1491838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1491838 prefixEnd_1491838 := by exact prefixLift 1491838
  have htrace : WordTrace (prefixWord ++ tailWord_1491838) baseStart_1491838 baseEnd_1491838 := by
    simpa [prefixWord, tailWord_1491838, baseEnd_1491838] using wordTrace_append hprefix tailTrace_1491838
  have hstable : (prefixWord ++ tailWord_1491838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491838).length < 2 ^ (prefixWord ++ tailWord_1491838).sum := by decide
  have hdescent : baseEnd_1491838 < baseStart_1491838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491860 : List Nat := [2, 4, 2, 1, 1, 1, 4, 1, 1, 4, 2]
def baseStart_1491860 : Nat := 118140960795 + 1491860 * 2 ^ 59
def prefixEnd_1491860 : Nat := 4983230072969 + 3 ^ 40 * 1491860 * 2
def baseEnd_1491860 : Nat := 766041249216638324589067

theorem tailTrace_1491860 : CollatzResearch.WordTrace tailWord_1491860 prefixEnd_1491860 766041249216638324589067 := by
  unfold tailWord_1491860
  simp only [CollatzResearch.WordTrace]
  refine ⟨27206302187626742124144517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36275069583502322832192689 27206302187626742124144517)
  ·
    refine ⟨5101181660180014148277097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27206302187626742124144517 5101181660180014148277097)
    ·
      refine ⟨3825886245135010611207823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5101181660180014148277097 3825886245135010611207823)
      ·
        refine ⟨5738829367702515916811735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3825886245135010611207823 5738829367702515916811735)
        ·
          refine ⟨8608244051553773875217603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5738829367702515916811735 8608244051553773875217603)
          ·
            refine ⟨12912366077330660812826405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8608244051553773875217603 12912366077330660812826405)
            ·
              refine ⟨2421068639499498902404951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12912366077330660812826405 2421068639499498902404951)
              ·
                refine ⟨3631602959249248353607427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2421068639499498902404951 3631602959249248353607427)
                ·
                  refine ⟨5447404438873872530411141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3631602959249248353607427 5447404438873872530411141)
                  ·
                    refine ⟨1021388332288851099452089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5447404438873872530411141 1021388332288851099452089)
                    ·
                      refine ⟨766041249216638324589067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1021388332288851099452089 766041249216638324589067)
                      ·
                        rfl

theorem cell23_1491860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 1, 1, 4, 2].length) (baseStart_1491860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1491860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1491860 prefixEnd_1491860 := by exact prefixLift 1491860
  have htrace : WordTrace (prefixWord ++ tailWord_1491860) baseStart_1491860 baseEnd_1491860 := by
    simpa [prefixWord, tailWord_1491860, baseEnd_1491860] using wordTrace_append hprefix tailTrace_1491860
  have hstable : (prefixWord ++ tailWord_1491860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491860).length < 2 ^ (prefixWord ++ tailWord_1491860).sum := by decide
  have hdescent : baseEnd_1491860 < baseStart_1491860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491876 : List Nat := [2, 3, 1, 2, 1, 2, 1, 2, 1, 5, 3]
def baseStart_1491876 : Nat := 118140960795 + 1491876 * 2 ^ 59
def prefixEnd_1491876 : Nat := 4983230072969 + 3 ^ 40 * 1491876 * 2
def baseEnd_1491876 : Nat := 766049464907110261988993

theorem tailTrace_1491876 : CollatzResearch.WordTrace tailWord_1491876 prefixEnd_1491876 766049464907110261988993 := by
  unfold tailWord_1491876
  simp only [CollatzResearch.WordTrace]
  refine ⟨27206593971597759490435741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36275458628797012653914321 27206593971597759490435741)
  ·
    refine ⟨10202472739349159808913403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27206593971597759490435741 10202472739349159808913403)
    ·
      refine ⟨15303709109023739713370105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10202472739349159808913403 15303709109023739713370105)
      ·
        refine ⟨11477781831767804785027579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15303709109023739713370105 11477781831767804785027579)
        ·
          refine ⟨17216672747651707177541369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11477781831767804785027579 17216672747651707177541369)
          ·
            refine ⟨12912504560738780383156027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17216672747651707177541369 12912504560738780383156027)
            ·
              refine ⟨19368756841108170574734041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12912504560738780383156027 19368756841108170574734041)
              ·
                refine ⟨14526567630831127931050531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19368756841108170574734041 14526567630831127931050531)
                ·
                  refine ⟨21789851446246691896575797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14526567630831127931050531 21789851446246691896575797)
                  ·
                    refine ⟨2042798573085627365303981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21789851446246691896575797 2042798573085627365303981)
                    ·
                      refine ⟨766049464907110261988993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2042798573085627365303981 766049464907110261988993)
                      ·
                        rfl

theorem cell23_1491876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 1, 5, 3].length) (baseStart_1491876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1491876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1491876 prefixEnd_1491876 := by exact prefixLift 1491876
  have htrace : WordTrace (prefixWord ++ tailWord_1491876) baseStart_1491876 baseEnd_1491876 := by
    simpa [prefixWord, tailWord_1491876, baseEnd_1491876] using wordTrace_append hprefix tailTrace_1491876
  have hstable : (prefixWord ++ tailWord_1491876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491876).length < 2 ^ (prefixWord ++ tailWord_1491876).sum := by decide
  have hdescent : baseEnd_1491876 < baseStart_1491876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491916 : List Nat := [2, 2, 1, 4, 1, 1, 1, 1, 3, 3, 4]
def baseStart_1491916 : Nat := 118140960795 + 1491916 * 2 ^ 59
def prefixEnd_1491916 : Nat := 4983230072969 + 3 ^ 40 * 1491916 * 2
def baseEnd_1491916 : Nat := 766070004133290105488809

theorem tailTrace_1491916 : CollatzResearch.WordTrace tailWord_1491916 prefixEnd_1491916 766070004133290105488809 := by
  unfold tailWord_1491916
  simp only [CollatzResearch.WordTrace]
  refine ⟨27207323431525302906163801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36276431242033737208218401 27207323431525302906163801)
  ·
    refine ⟨20405492573643977179622851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27207323431525302906163801 20405492573643977179622851)
    ·
      refine ⟨30608238860465965769434277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20405492573643977179622851 30608238860465965769434277)
      ·
        refine ⟨5739044786337368581768927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30608238860465965769434277 5739044786337368581768927)
        ·
          refine ⟨8608567179506052872653391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5739044786337368581768927 8608567179506052872653391)
          ·
            refine ⟨12912850769259079308980087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8608567179506052872653391 12912850769259079308980087)
            ·
              refine ⟨19369276153888618963470131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12912850769259079308980087 19369276153888618963470131)
              ·
                refine ⟨29053914230832928445205197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19369276153888618963470131 29053914230832928445205197)
                ·
                  refine ⟨10895217836562348166951949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29053914230832928445205197 10895217836562348166951949)
                  ·
                    refine ⟨4085706688710880562606981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10895217836562348166951949 4085706688710880562606981)
                    ·
                      refine ⟨766070004133290105488809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4085706688710880562606981 766070004133290105488809)
                      ·
                        rfl

theorem cell23_1491916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_1491916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1491916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1491916 prefixEnd_1491916 := by exact prefixLift 1491916
  have htrace : WordTrace (prefixWord ++ tailWord_1491916) baseStart_1491916 baseEnd_1491916 := by
    simpa [prefixWord, tailWord_1491916, baseEnd_1491916] using wordTrace_append hprefix tailTrace_1491916
  have hstable : (prefixWord ++ tailWord_1491916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491916).length < 2 ^ (prefixWord ++ tailWord_1491916).sum := by decide
  have hdescent : baseEnd_1491916 < baseStart_1491916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491933 : List Nat := [1, 4, 3, 1, 2, 1, 2, 1, 1, 3, 4]
def baseStart_1491933 : Nat := 118140960795 + 1491933 * 2 ^ 59
def prefixEnd_1491933 : Nat := 4983230072969 + 3 ^ 40 * 1491933 * 2
def baseEnd_1491933 : Nat := 766078733304416538976231

theorem tailTrace_1491933 : CollatzResearch.WordTrace tailWord_1491933 prefixEnd_1491933 766078733304416538976231 := by
  unfold tailWord_1491933
  simp only [CollatzResearch.WordTrace]
  refine ⟨54415266903989017715696453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36276844602659345143797635 54415266903989017715696453)
  ·
    refine ⟨10202862544497940821693085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54415266903989017715696453 10202862544497940821693085)
    ·
      refine ⟨3826073454186727808134907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10202862544497940821693085 3826073454186727808134907)
      ·
        refine ⟨5739110181280091712202361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3826073454186727808134907 5739110181280091712202361)
        ·
          refine ⟨4304332635960068784151771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5739110181280091712202361 4304332635960068784151771)
          ·
            refine ⟨6456498953940103176227657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4304332635960068784151771 6456498953940103176227657)
            ·
              refine ⟨4842374215455077382170743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6456498953940103176227657 4842374215455077382170743)
              ·
                refine ⟨7263561323182616073256115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4842374215455077382170743 7263561323182616073256115)
                ·
                  refine ⟨10895341984773924109884173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7263561323182616073256115 10895341984773924109884173)
                  ·
                    refine ⟨4085753244290221541206565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10895341984773924109884173 4085753244290221541206565)
                    ·
                      refine ⟨766078733304416538976231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4085753244290221541206565 766078733304416538976231)
                      ·
                        rfl

theorem cell23_1491933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_1491933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1491933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1491933 prefixEnd_1491933 := by exact prefixLift 1491933
  have htrace : WordTrace (prefixWord ++ tailWord_1491933) baseStart_1491933 baseEnd_1491933 := by
    simpa [prefixWord, tailWord_1491933, baseEnd_1491933] using wordTrace_append hprefix tailTrace_1491933
  have hstable : (prefixWord ++ tailWord_1491933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491933).length < 2 ^ (prefixWord ++ tailWord_1491933).sum := by decide
  have hdescent : baseEnd_1491933 < baseStart_1491933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491950 : List Nat := [4, 1, 2, 1, 4, 1, 1, 2, 2, 1, 4]
def baseStart_1491950 : Nat := 118140960795 + 1491950 * 2 ^ 59
def prefixEnd_1491950 : Nat := 4983230072969 + 3 ^ 40 * 1491950 * 2
def baseEnd_1491950 : Nat := 766087462475542972463653

theorem tailTrace_1491950 : CollatzResearch.WordTrace tailWord_1491950 prefixEnd_1491950 766087462475542972463653 := by
  unfold tailWord_1491950
  simp only [CollatzResearch.WordTrace]
  refine ⟨6801985868115928702383163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36277257963284953079376869 6801985868115928702383163)
  ·
    refine ⟨10202978802173893053574745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6801985868115928702383163 10202978802173893053574745)
    ·
      refine ⟨7652234101630419790181059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10202978802173893053574745 7652234101630419790181059)
      ·
        refine ⟨11478351152445629685271589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7652234101630419790181059 11478351152445629685271589)
        ·
          refine ⟨2152190841083555565988423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11478351152445629685271589 2152190841083555565988423)
          ·
            refine ⟨3228286261625333348982635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2152190841083555565988423 3228286261625333348982635)
            ·
              refine ⟨4842429392438000023473953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3228286261625333348982635 4842429392438000023473953)
              ·
                refine ⟨3631822044328500017605465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4842429392438000023473953 3631822044328500017605465)
                ·
                  refine ⟨2723866533246375013204099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3631822044328500017605465 2723866533246375013204099)
                  ·
                    refine ⟨4085799799869562519806149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2723866533246375013204099 4085799799869562519806149)
                    ·
                      refine ⟨766087462475542972463653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4085799799869562519806149 766087462475542972463653)
                      ·
                        rfl

theorem cell23_1491950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 2, 2, 1, 4].length) (baseStart_1491950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1491950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1491950 prefixEnd_1491950 := by exact prefixLift 1491950
  have htrace : WordTrace (prefixWord ++ tailWord_1491950) baseStart_1491950 baseEnd_1491950 := by
    simpa [prefixWord, tailWord_1491950, baseEnd_1491950] using wordTrace_append hprefix tailTrace_1491950
  have hstable : (prefixWord ++ tailWord_1491950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491950).length < 2 ^ (prefixWord ++ tailWord_1491950).sum := by decide
  have hdescent : baseEnd_1491950 < baseStart_1491950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491953 : List Nat := [1, 2, 2, 2, 4, 1, 1, 1, 4, 2, 3]
def baseStart_1491953 : Nat := 118140960795 + 1491953 * 2 ^ 59
def prefixEnd_1491953 : Nat := 4983230072969 + 3 ^ 40 * 1491953 * 2
def baseEnd_1491953 : Nat := 766089002917506460726139

theorem tailTrace_1491953 : CollatzResearch.WordTrace tailWord_1491953 prefixEnd_1491953 766089002917506460726139 := by
  unfold tailWord_1491953
  simp only [CollatzResearch.WordTrace]
  refine ⟨54415996363916561131424513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36277330909277707420949675 54415996363916561131424513)
  ·
    refine ⟨40811997272937420848568385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54415996363916561131424513 40811997272937420848568385)
    ·
      refine ⟨30608997954703065636426289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40811997272937420848568385 30608997954703065636426289)
      ·
        refine ⟨22956748466027299227319717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30608997954703065636426289 22956748466027299227319717)
        ·
          refine ⟨4304390337380118605122447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22956748466027299227319717 4304390337380118605122447)
          ·
            refine ⟨6456585506070177907683671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4304390337380118605122447 6456585506070177907683671)
            ·
              refine ⟨9684878259105266861525507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6456585506070177907683671 9684878259105266861525507)
              ·
                refine ⟨14527317388657900292288261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9684878259105266861525507 14527317388657900292288261)
                ·
                  refine ⟨2723872010373356304804049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14527317388657900292288261 2723872010373356304804049)
                  ·
                    refine ⟨2042904007780017228603037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2723872010373356304804049 2042904007780017228603037)
                    ·
                      refine ⟨766089002917506460726139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2042904007780017228603037 766089002917506460726139)
                      ·
                        rfl

theorem cell23_1491953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 4, 2, 3].length) (baseStart_1491953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1491953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1491953 prefixEnd_1491953 := by exact prefixLift 1491953
  have htrace : WordTrace (prefixWord ++ tailWord_1491953) baseStart_1491953 baseEnd_1491953 := by
    simpa [prefixWord, tailWord_1491953, baseEnd_1491953] using wordTrace_append hprefix tailTrace_1491953
  have hstable : (prefixWord ++ tailWord_1491953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491953).length < 2 ^ (prefixWord ++ tailWord_1491953).sum := by decide
  have hdescent : baseEnd_1491953 < baseStart_1491953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1491993 : List Nat := [1, 2, 1, 2, 1, 1, 4, 3, 1, 5, 2]
def baseStart_1491993 : Nat := 118140960795 + 1491993 * 2 ^ 59
def prefixEnd_1491993 : Nat := 4983230072969 + 3 ^ 40 * 1491993 * 2
def baseEnd_1491993 : Nat := 766109542143686304225955

theorem tailTrace_1491993 : CollatzResearch.WordTrace tailWord_1491993 prefixEnd_1491993 766109542143686304225955 := by
  unfold tailWord_1491993
  simp only [CollatzResearch.WordTrace]
  refine ⟨54417455283771647962880633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36278303522514431975253755 54417455283771647962880633)
  ·
    refine ⟨40813091462828735972160475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54417455283771647962880633 40813091462828735972160475)
    ·
      refine ⟨61219637194243103958240713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40813091462828735972160475 61219637194243103958240713)
      ·
        refine ⟨45914727895682327968680535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61219637194243103958240713 45914727895682327968680535)
        ·
          refine ⟨68872091843523491953020803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45914727895682327968680535 68872091843523491953020803)
          ·
            refine ⟨103308137765285237929531205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68872091843523491953020803 103308137765285237929531205)
            ·
              refine ⟨19370275830990982111787101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103308137765285237929531205 19370275830990982111787101)
              ·
                refine ⟨7263853436621618291920163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19370275830990982111787101 7263853436621618291920163)
                ·
                  refine ⟨10895780154932427437880245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7263853436621618291920163 10895780154932427437880245)
                  ·
                    refine ⟨1021479389524915072301273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10895780154932427437880245 1021479389524915072301273)
                    ·
                      refine ⟨766109542143686304225955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1021479389524915072301273 766109542143686304225955)
                      ·
                        rfl

theorem cell23_1491993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 5, 2].length) (baseStart_1491993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1491993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1491993 prefixEnd_1491993 := by exact prefixLift 1491993
  have htrace : WordTrace (prefixWord ++ tailWord_1491993) baseStart_1491993 baseEnd_1491993 := by
    simpa [prefixWord, tailWord_1491993, baseEnd_1491993] using wordTrace_append hprefix tailTrace_1491993
  have hstable : (prefixWord ++ tailWord_1491993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1491993).length < 2 ^ (prefixWord ++ tailWord_1491993).sum := by decide
  have hdescent : baseEnd_1491993 < baseStart_1491993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1491993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492016 : List Nat := [2, 1, 1, 1, 2, 4, 1, 2, 3, 6]
def baseStart_1492016 : Nat := 118140960795 + 1492016 * 2 ^ 59
def prefixEnd_1492016 : Nat := 4983230072969 + 3 ^ 40 * 1492016 * 2
def baseEnd_1492016 : Nat := 255373784066246571412783

theorem tailTrace_1492016 : CollatzResearch.WordTrace tailWord_1492016 prefixEnd_1492016 255373784066246571412783 := by
  unfold tailWord_1492016
  simp only [CollatzResearch.WordTrace]
  refine ⟨27209147081344161445483951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36278862775125548593978601 27209147081344161445483951)
  ·
    refine ⟨40813720622016242168225927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27209147081344161445483951 40813720622016242168225927)
    ·
      refine ⟨61220580933024363252338891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40813720622016242168225927 61220580933024363252338891)
      ·
        refine ⟨91830871399536544878508337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61220580933024363252338891 91830871399536544878508337)
        ·
          refine ⟨68873153549652408658881253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91830871399536544878508337 68873153549652408658881253)
          ·
            refine ⟨12913716290559826623540235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68873153549652408658881253 12913716290559826623540235)
            ·
              refine ⟨19370574435839739935310353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12913716290559826623540235 19370574435839739935310353)
              ·
                refine ⟨14527930826879804951482765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19370574435839739935310353 14527930826879804951482765)
                ·
                  refine ⟨5447974060079926856806037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14527930826879804951482765 5447974060079926856806037)
                  ·
                    refine ⟨255373784066246571412783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5447974060079926856806037 255373784066246571412783)
                    ·
                      rfl

theorem cell23_1492016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 3, 6].length) (baseStart_1492016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1492016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1492016 prefixEnd_1492016 := by exact prefixLift 1492016
  have htrace : WordTrace (prefixWord ++ tailWord_1492016) baseStart_1492016 baseEnd_1492016 := by
    simpa [prefixWord, tailWord_1492016, baseEnd_1492016] using wordTrace_append hprefix tailTrace_1492016
  have hstable : (prefixWord ++ tailWord_1492016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492016).length < 2 ^ (prefixWord ++ tailWord_1492016).sum := by decide
  have hdescent : baseEnd_1492016 < baseStart_1492016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492017 : List Nat := [1, 2, 2, 3, 1, 2, 3, 4, 1, 1, 3]
def baseStart_1492017 : Nat := 118140960795 + 1492017 * 2 ^ 59
def prefixEnd_1492017 : Nat := 4983230072969 + 3 ^ 40 * 1492017 * 2
def baseEnd_1492017 : Nat := 766121865679394210325845

theorem tailTrace_1492017 : CollatzResearch.WordTrace tailWord_1492017 prefixEnd_1492017 766121865679394210325845 := by
  unfold tailWord_1492017
  simp only [CollatzResearch.WordTrace]
  refine ⟨54418330635684700061754305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36278887090456466707836203 54418330635684700061754305)
  ·
    refine ⟨40813747976763525046315729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54418330635684700061754305 40813747976763525046315729)
    ·
      refine ⟨30610310982572643784736797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40813747976763525046315729 30610310982572643784736797)
      ·
        refine ⟨11478866618464741419276299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30610310982572643784736797 11478866618464741419276299)
        ·
          refine ⟨17218299927697112128914449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11478866618464741419276299 17218299927697112128914449)
          ·
            refine ⟨12913724945772834096685837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17218299927697112128914449 12913724945772834096685837)
            ·
              refine ⟨4842646854664812786257189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12913724945772834096685837 4842646854664812786257189)
              ·
                refine ⟨907996285249652397423223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4842646854664812786257189 907996285249652397423223)
                ·
                  refine ⟨1361994427874478596134835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 907996285249652397423223 1361994427874478596134835)
                  ·
                    refine ⟨2042991641811717894202253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1361994427874478596134835 2042991641811717894202253)
                    ·
                      refine ⟨766121865679394210325845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2042991641811717894202253 766121865679394210325845)
                      ·
                        rfl

theorem cell23_1492017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 4, 1, 1, 3].length) (baseStart_1492017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1492017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1492017 prefixEnd_1492017 := by exact prefixLift 1492017
  have htrace : WordTrace (prefixWord ++ tailWord_1492017) baseStart_1492017 baseEnd_1492017 := by
    simpa [prefixWord, tailWord_1492017, baseEnd_1492017] using wordTrace_append hprefix tailTrace_1492017
  have hstable : (prefixWord ++ tailWord_1492017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492017).length < 2 ^ (prefixWord ++ tailWord_1492017).sum := by decide
  have hdescent : baseEnd_1492017 < baseStart_1492017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492020 : List Nat := [2, 5, 1, 2, 1, 1, 1, 2, 3, 5]
def baseStart_1492020 : Nat := 118140960795 + 1492020 * 2 ^ 59
def prefixEnd_1492020 : Nat := 4983230072969 + 3 ^ 40 * 1492020 * 2
def baseEnd_1492020 : Nat := 255374468707119232862777

theorem tailTrace_1492020 : CollatzResearch.WordTrace tailWord_1492020 prefixEnd_1492020 255374468707119232862777 := by
  unfold tailWord_1492020
  simp only [CollatzResearch.WordTrace]
  refine ⟨27209220027336915787056757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36278960036449221049409009 27209220027336915787056757)
  ·
    refine ⟨2550864377562835855036571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27209220027336915787056757 2550864377562835855036571)
    ·
      refine ⟨3826296566344253782554857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2550864377562835855036571 3826296566344253782554857)
      ·
        refine ⟨2869722424758190336916143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3826296566344253782554857 2869722424758190336916143)
        ·
          refine ⟨4304583637137285505374215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2869722424758190336916143 4304583637137285505374215)
          ·
            refine ⟨6456875455705928258061323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4304583637137285505374215 6456875455705928258061323)
            ·
              refine ⟨9685313183558892387091985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6456875455705928258061323 9685313183558892387091985)
              ·
                refine ⟨7263984887669169290318989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9685313183558892387091985 7263984887669169290318989)
                ·
                  refine ⟨2723994332875938483869621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7263984887669169290318989 2723994332875938483869621)
                  ·
                    refine ⟨255374468707119232862777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2723994332875938483869621 255374468707119232862777)
                    ·
                      rfl

theorem cell23_1492020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_1492020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1492020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1492020 prefixEnd_1492020 := by exact prefixLift 1492020
  have htrace : WordTrace (prefixWord ++ tailWord_1492020) baseStart_1492020 baseEnd_1492020 := by
    simpa [prefixWord, tailWord_1492020, baseEnd_1492020] using wordTrace_append hprefix tailTrace_1492020
  have hstable : (prefixWord ++ tailWord_1492020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492020).length < 2 ^ (prefixWord ++ tailWord_1492020).sum := by decide
  have hdescent : baseEnd_1492020 < baseStart_1492020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492023 : List Nat := [1, 1, 3, 1, 2, 2, 1, 2, 2, 6, 2]
def baseStart_1492023 : Nat := 118140960795 + 1492023 * 2 ^ 59
def prefixEnd_1492023 : Nat := 4983230072969 + 3 ^ 40 * 1492023 * 2
def baseEnd_1492023 : Nat := 766124946563321186850817

theorem tailTrace_1492023 : CollatzResearch.WordTrace tailWord_1492023 prefixEnd_1492023 766124946563321186850817 := by
  unfold tailWord_1492023
  simp only [CollatzResearch.WordTrace]
  refine ⟨54418549473662963086472723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36279032982441975390981815 54418549473662963086472723)
  ·
    refine ⟨81627824210494444629709085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54418549473662963086472723 81627824210494444629709085)
    ·
      refine ⟨30610434078935416736140907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81627824210494444629709085 30610434078935416736140907)
      ·
        refine ⟨45915651118403125104211361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30610434078935416736140907 45915651118403125104211361)
        ·
          refine ⟨34436738338802343828158521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45915651118403125104211361 34436738338802343828158521)
          ·
            refine ⟨25827553754101757871118891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34436738338802343828158521 25827553754101757871118891)
            ·
              refine ⟨38741330631152636806678337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25827553754101757871118891 38741330631152636806678337)
              ·
                refine ⟨29055997973364477605008753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38741330631152636806678337 29055997973364477605008753)
                ·
                  refine ⟨21791998480023358203756565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29055997973364477605008753 21791998480023358203756565)
                  ·
                    refine ⟨1021499928751094915801089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21791998480023358203756565 1021499928751094915801089)
                    ·
                      refine ⟨766124946563321186850817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1021499928751094915801089 766124946563321186850817)
                      ·
                        rfl

theorem cell23_1492023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 6, 2].length) (baseStart_1492023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1492023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1492023 prefixEnd_1492023 := by exact prefixLift 1492023
  have htrace : WordTrace (prefixWord ++ tailWord_1492023) baseStart_1492023 baseEnd_1492023 := by
    simpa [prefixWord, tailWord_1492023, baseEnd_1492023] using wordTrace_append hprefix tailTrace_1492023
  have hstable : (prefixWord ++ tailWord_1492023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492023).length < 2 ^ (prefixWord ++ tailWord_1492023).sum := by decide
  have hdescent : baseEnd_1492023 < baseStart_1492023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492053 : List Nat := [1, 3, 2, 2, 1, 2, 1, 4, 1, 2, 4]
def baseStart_1492053 : Nat := 118140960795 + 1492053 * 2 ^ 59
def prefixEnd_1492053 : Nat := 4983230072969 + 3 ^ 40 * 1492053 * 2
def baseEnd_1492053 : Nat := 766140350982956069475679

theorem tailTrace_1492053 : CollatzResearch.WordTrace tailWord_1492053 prefixEnd_1492053 766140350982956069475679 := by
  unfold tailWord_1492053
  simp only [CollatzResearch.WordTrace]
  refine ⟨54419643663554278210064813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36279762442369518806709875 54419643663554278210064813)
  ·
    refine ⟨20407366373832854328774305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54419643663554278210064813 20407366373832854328774305)
    ·
      refine ⟨15305524780374640746580729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20407366373832854328774305 15305524780374640746580729)
      ·
        refine ⟨11479143585280980559935547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15305524780374640746580729 11479143585280980559935547)
        ·
          refine ⟨17218715377921470839903321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11479143585280980559935547 17218715377921470839903321)
          ·
            refine ⟨12914036533441103129927491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17218715377921470839903321 12914036533441103129927491)
            ·
              refine ⟨19371054800161654694891237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12914036533441103129927491 19371054800161654694891237)
              ·
                refine ⟨3632072775030310255292107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19371054800161654694891237 3632072775030310255292107)
                ·
                  refine ⟨5448109162545465382938161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3632072775030310255292107 5448109162545465382938161)
                  ·
                    refine ⟨4086081871909099037203621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5448109162545465382938161 4086081871909099037203621)
                    ·
                      refine ⟨766140350982956069475679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4086081871909099037203621 766140350982956069475679)
                      ·
                        rfl

theorem cell23_1492053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_1492053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1492053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1492053 prefixEnd_1492053 := by exact prefixLift 1492053
  have htrace : WordTrace (prefixWord ++ tailWord_1492053) baseStart_1492053 baseEnd_1492053 := by
    simpa [prefixWord, tailWord_1492053, baseEnd_1492053] using wordTrace_append hprefix tailTrace_1492053
  have hstable : (prefixWord ++ tailWord_1492053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492053).length < 2 ^ (prefixWord ++ tailWord_1492053).sum := by decide
  have hdescent : baseEnd_1492053 < baseStart_1492053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492054 : List Nat := [5, 2, 2, 1, 2, 1, 1, 3, 1, 5]
def baseStart_1492054 : Nat := 118140960795 + 1492054 * 2 ^ 59
def prefixEnd_1492054 : Nat := 4983230072969 + 3 ^ 40 * 1492054 * 2
def baseEnd_1492054 : Nat := 255380288154536855187725

theorem tailTrace_1492054 : CollatzResearch.WordTrace tailWord_1492054 prefixEnd_1492054 255380288154536855187725 := by
  unfold tailWord_1492054
  simp only [CollatzResearch.WordTrace]
  refine ⟨3401230008534415961303201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36279786757700436920567477 3401230008534415961303201)
  ·
    refine ⟨2550922506400811970977401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3401230008534415961303201 2550922506400811970977401)
    ·
      refine ⟨1913191879800608978233051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2550922506400811970977401 1913191879800608978233051)
      ·
        refine ⟨2869787819700913467349577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1913191879800608978233051 2869787819700913467349577)
        ·
          refine ⟨2152340864775685100512183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2869787819700913467349577 2152340864775685100512183)
          ·
            refine ⟨3228511297163527650768275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2152340864775685100512183 3228511297163527650768275)
            ·
              refine ⟨4842766945745291476152413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3228511297163527650768275 4842766945745291476152413)
              ·
                refine ⟨1816037604654484303557155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4842766945745291476152413 1816037604654484303557155)
                ·
                  refine ⟨2724056406981726455335733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1816037604654484303557155 2724056406981726455335733)
                  ·
                    refine ⟨255380288154536855187725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2724056406981726455335733 255380288154536855187725)
                    ·
                      rfl

theorem cell23_1492054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_1492054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1492054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1492054 prefixEnd_1492054 := by exact prefixLift 1492054
  have htrace : WordTrace (prefixWord ++ tailWord_1492054) baseStart_1492054 baseEnd_1492054 := by
    simpa [prefixWord, tailWord_1492054, baseEnd_1492054] using wordTrace_append hprefix tailTrace_1492054
  have hstable : (prefixWord ++ tailWord_1492054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492054).length < 2 ^ (prefixWord ++ tailWord_1492054).sum := by decide
  have hdescent : baseEnd_1492054 < baseStart_1492054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492074 : List Nat := [3, 1, 3, 2, 2, 2, 2, 1, 3, 2, 2]
def baseStart_1492074 : Nat := 118140960795 + 1492074 * 2 ^ 59
def prefixEnd_1492074 : Nat := 4983230072969 + 3 ^ 40 * 1492074 * 2
def baseEnd_1492074 : Nat := 766151134076700487313083

theorem tailTrace_1492074 : CollatzResearch.WordTrace tailWord_1492074 prefixEnd_1492074 766151134076700487313083 := by
  unfold tailWord_1492074
  simp only [CollatzResearch.WordTrace]
  refine ⟨13605102399119549699144819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36280273064318799197719517 13605102399119549699144819)
  ·
    refine ⟨20407653598679324548717229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13605102399119549699144819 20407653598679324548717229)
    ·
      refine ⟨7652870099504746705768961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20407653598679324548717229 7652870099504746705768961)
      ·
        refine ⟨5739652574628560029326721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7652870099504746705768961 5739652574628560029326721)
        ·
          refine ⟨4304739430971420021995041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5739652574628560029326721 4304739430971420021995041)
          ·
            refine ⟨3228554573228565016496281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4304739430971420021995041 3228554573228565016496281)
            ·
              refine ⟨2421415929921423762372211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3228554573228565016496281 2421415929921423762372211)
              ·
                refine ⟨3632123894882135643558317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2421415929921423762372211 3632123894882135643558317)
                ·
                  refine ⟨1362046460580800866334369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3632123894882135643558317 1362046460580800866334369)
                  ·
                    refine ⟨1021534845435600649750777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1362046460580800866334369 1021534845435600649750777)
                    ·
                      refine ⟨766151134076700487313083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1021534845435600649750777 766151134076700487313083)
                      ·
                        rfl

theorem cell23_1492074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 1, 3, 2, 2].length) (baseStart_1492074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1492074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1492074 prefixEnd_1492074 := by exact prefixLift 1492074
  have htrace : WordTrace (prefixWord ++ tailWord_1492074) baseStart_1492074 baseEnd_1492074 := by
    simpa [prefixWord, tailWord_1492074, baseEnd_1492074] using wordTrace_append hprefix tailTrace_1492074
  have hstable : (prefixWord ++ tailWord_1492074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492074).length < 2 ^ (prefixWord ++ tailWord_1492074).sum := by decide
  have hdescent : baseEnd_1492074 < baseStart_1492074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492143 : List Nat := [1, 1, 2, 1, 2, 3, 2, 3, 2, 2, 4]
def baseStart_1492143 : Nat := 118140960795 + 1492143 * 2 ^ 59
def prefixEnd_1492143 : Nat := 4983230072969 + 3 ^ 40 * 1492143 * 2
def baseEnd_1492143 : Nat := 766186564241860717350265

theorem tailTrace_1492143 : CollatzResearch.WordTrace tailWord_1492143 prefixEnd_1492143 766186564241860717350265 := by
  unfold tailWord_1492143
  simp only [CollatzResearch.WordTrace]
  refine ⟨54422926233228223580841083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36281950822152149053894055 54422926233228223580841083)
  ·
    refine ⟨81634389349842335371261625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54422926233228223580841083 81634389349842335371261625)
    ·
      refine ⟨61225792012381751528446219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81634389349842335371261625 61225792012381751528446219)
      ·
        refine ⟨91838688018572627292669329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61225792012381751528446219 91838688018572627292669329)
        ·
          refine ⟨68879016013929470469501997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91838688018572627292669329 68879016013929470469501997)
          ·
            refine ⟨25829631005223551426063249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68879016013929470469501997 25829631005223551426063249)
            ·
              refine ⟨19372223253917663569547437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25829631005223551426063249 19372223253917663569547437)
              ·
                refine ⟨7264583720219123838580289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19372223253917663569547437 7264583720219123838580289)
                ·
                  refine ⟨5448437790164342878935217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7264583720219123838580289 5448437790164342878935217)
                  ·
                    refine ⟨4086328342623257159201413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5448437790164342878935217 4086328342623257159201413)
                    ·
                      refine ⟨766186564241860717350265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4086328342623257159201413 766186564241860717350265)
                      ·
                        rfl

theorem cell23_1492143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 2, 2, 4].length) (baseStart_1492143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1492143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1492143 prefixEnd_1492143 := by exact prefixLift 1492143
  have htrace : WordTrace (prefixWord ++ tailWord_1492143) baseStart_1492143 baseEnd_1492143 := by
    simpa [prefixWord, tailWord_1492143, baseEnd_1492143] using wordTrace_append hprefix tailTrace_1492143
  have hstable : (prefixWord ++ tailWord_1492143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492143).length < 2 ^ (prefixWord ++ tailWord_1492143).sum := by decide
  have hdescent : baseEnd_1492143 < baseStart_1492143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492163 : List Nat := [1, 1, 1, 3, 1, 1, 1, 3, 3, 5, 3]
def baseStart_1492163 : Nat := 118140960795 + 1492163 * 2 ^ 59
def prefixEnd_1492163 : Nat := 4983230072969 + 3 ^ 40 * 1492163 * 2
def baseEnd_1492163 : Nat := 766196833854950639100173

theorem tailTrace_1492163 : CollatzResearch.WordTrace tailWord_1492163 prefixEnd_1492163 766196833854950639100173 := by
  unfold tailWord_1492163
  simp only [CollatzResearch.WordTrace]
  refine ⟨54423655693155766996569143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36282437128770511331046095 54423655693155766996569143)
  ·
    refine ⟨81635483539733650494853715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54423655693155766996569143 81635483539733650494853715)
    ·
      refine ⟨122453225309600475742280573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81635483539733650494853715 122453225309600475742280573)
      ·
        refine ⟨45919959491100178403355215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122453225309600475742280573 45919959491100178403355215)
        ·
          refine ⟨68879939236650267605032823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45919959491100178403355215 68879939236650267605032823)
          ·
            refine ⟨103319908854975401407549235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68879939236650267605032823 103319908854975401407549235)
            ·
              refine ⟨154979863282463102111323853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103319908854975401407549235 154979863282463102111323853)
              ·
                refine ⟨58117448730923663291746445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 154979863282463102111323853 58117448730923663291746445)
                ·
                  refine ⟨21794043274096373734404917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58117448730923663291746445 21794043274096373734404917)
                  ·
                    refine ⟨2043191556946535037600461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21794043274096373734404917 2043191556946535037600461)
                    ·
                      refine ⟨766196833854950639100173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2043191556946535037600461 766196833854950639100173)
                      ·
                        rfl

theorem cell23_1492163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 5, 3].length) (baseStart_1492163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1492163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1492163 prefixEnd_1492163 := by exact prefixLift 1492163
  have htrace : WordTrace (prefixWord ++ tailWord_1492163) baseStart_1492163 baseEnd_1492163 := by
    simpa [prefixWord, tailWord_1492163, baseEnd_1492163] using wordTrace_append hprefix tailTrace_1492163
  have hstable : (prefixWord ++ tailWord_1492163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492163).length < 2 ^ (prefixWord ++ tailWord_1492163).sum := by decide
  have hdescent : baseEnd_1492163 < baseStart_1492163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492164 : List Nat := [2, 3, 3, 1, 3, 1, 1, 2, 1, 4, 2]
def baseStart_1492164 : Nat := 118140960795 + 1492164 * 2 ^ 59
def prefixEnd_1492164 : Nat := 4983230072969 + 3 ^ 40 * 1492164 * 2
def baseEnd_1492164 : Nat := 766197347335605135187669

theorem tailTrace_1492164 : CollatzResearch.WordTrace tailWord_1492164 prefixEnd_1492164 766197347335605135187669 := by
  unfold tailWord_1492164
  simp only [CollatzResearch.WordTrace]
  refine ⟨27211846083076072083677773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36282461444101429444903697 27211846083076072083677773)
  ·
    refine ⟨10204442281153527031379165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27211846083076072083677773 10204442281153527031379165)
    ·
      refine ⟨3826665855432572636767187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10204442281153527031379165 3826665855432572636767187)
      ·
        refine ⟨5739998783148858955150781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3826665855432572636767187 5739998783148858955150781)
        ·
          refine ⟨2152499543680822108181543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5739998783148858955150781 2152499543680822108181543)
          ·
            refine ⟨3228749315521233162272315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2152499543680822108181543 3228749315521233162272315)
            ·
              refine ⟨4843123973281849743408473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3228749315521233162272315 4843123973281849743408473)
              ·
                refine ⟨3632342979961387307556355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4843123973281849743408473 3632342979961387307556355)
                ·
                  refine ⟨5448514469942080961334533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3632342979961387307556355 5448514469942080961334533)
                  ·
                    refine ⟨1021596463114140180250225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5448514469942080961334533 1021596463114140180250225)
                    ·
                      refine ⟨766197347335605135187669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1021596463114140180250225 766197347335605135187669)
                      ·
                        rfl

theorem cell23_1492164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 2, 1, 4, 2].length) (baseStart_1492164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1492164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1492164 prefixEnd_1492164 := by exact prefixLift 1492164
  have htrace : WordTrace (prefixWord ++ tailWord_1492164) baseStart_1492164 baseEnd_1492164 := by
    simpa [prefixWord, tailWord_1492164, baseEnd_1492164] using wordTrace_append hprefix tailTrace_1492164
  have hstable : (prefixWord ++ tailWord_1492164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492164).length < 2 ^ (prefixWord ++ tailWord_1492164).sum := by decide
  have hdescent : baseEnd_1492164 < baseStart_1492164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492181 : List Nat := [1, 3, 2, 4, 1, 2, 2, 2, 2, 2, 2]
def baseStart_1492181 : Nat := 118140960795 + 1492181 * 2 ^ 59
def prefixEnd_1492181 : Nat := 4983230072969 + 3 ^ 40 * 1492181 * 2
def baseEnd_1492181 : Nat := 766206076506731568675091

theorem tailTrace_1492181 : CollatzResearch.WordTrace tailWord_1492181 prefixEnd_1492181 766206076506731568675091 := by
  unfold tailWord_1492181
  simp only [CollatzResearch.WordTrace]
  refine ⟨54424312207090556070724397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36282874804727037380482931 54424312207090556070724397)
  ·
    refine ⟨20409117077658958526521649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54424312207090556070724397 20409117077658958526521649)
    ·
      refine ⟨15306837808244218894891237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20409117077658958526521649 15306837808244218894891237)
      ·
        refine ⟨2870032089045791042792107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15306837808244218894891237 2870032089045791042792107)
        ·
          refine ⟨4305048133568686564188161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2870032089045791042792107 4305048133568686564188161)
          ·
            refine ⟨3228786100176514923141121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4305048133568686564188161 3228786100176514923141121)
            ·
              refine ⟨2421589575132386192355841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3228786100176514923141121 2421589575132386192355841)
              ·
                refine ⟨1816192181349289644266881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2421589575132386192355841 1816192181349289644266881)
                ·
                  refine ⟨1362144136011967233200161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1816192181349289644266881 1362144136011967233200161)
                  ·
                    refine ⟨1021608102008975424900121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1362144136011967233200161 1021608102008975424900121)
                    ·
                      refine ⟨766206076506731568675091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1021608102008975424900121 766206076506731568675091)
                      ·
                        rfl

theorem cell23_1492181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_1492181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1492181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1492181 prefixEnd_1492181 := by exact prefixLift 1492181
  have htrace : WordTrace (prefixWord ++ tailWord_1492181) baseStart_1492181 baseEnd_1492181 := by
    simpa [prefixWord, tailWord_1492181, baseEnd_1492181] using wordTrace_append hprefix tailTrace_1492181
  have hstable : (prefixWord ++ tailWord_1492181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492181).length < 2 ^ (prefixWord ++ tailWord_1492181).sum := by decide
  have hdescent : baseEnd_1492181 < baseStart_1492181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492197 : List Nat := [1, 3, 1, 4, 3, 1, 1, 1, 2, 3, 3]
def baseStart_1492197 : Nat := 118140960795 + 1492197 * 2 ^ 59
def prefixEnd_1492197 : Nat := 4983230072969 + 3 ^ 40 * 1492197 * 2
def baseEnd_1492197 : Nat := 766214292197203506075017

theorem tailTrace_1492197 : CollatzResearch.WordTrace tailWord_1492197 prefixEnd_1492197 766214292197203506075017 := by
  unfold tailWord_1492197
  simp only [CollatzResearch.WordTrace]
  refine ⟨54424895775032590803306845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36283263850021727202204563 54424895775032590803306845)
  ·
    refine ⟨20409335915637221551240067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54424895775032590803306845 20409335915637221551240067)
    ·
      refine ⟨30614003873455832326860101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20409335915637221551240067 30614003873455832326860101)
      ·
        refine ⟨5740125726272968561286269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30614003873455832326860101 5740125726272968561286269)
        ·
          refine ⟨2152547147352363210482351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5740125726272968561286269 2152547147352363210482351)
          ·
            refine ⟨3228820721028544815723527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2152547147352363210482351 3228820721028544815723527)
            ·
              refine ⟨4843231081542817223585291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3228820721028544815723527 4843231081542817223585291)
              ·
                refine ⟨7264846622314225835377937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4843231081542817223585291 7264846622314225835377937)
                ·
                  refine ⟨5448634966735669376533453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7264846622314225835377937 5448634966735669376533453)
                  ·
                    refine ⟨2043238112525876016200045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5448634966735669376533453 2043238112525876016200045)
                    ·
                      refine ⟨766214292197203506075017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2043238112525876016200045 766214292197203506075017)
                      ·
                        rfl

theorem cell23_1492197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_1492197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1492197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1492197 prefixEnd_1492197 := by exact prefixLift 1492197
  have htrace : WordTrace (prefixWord ++ tailWord_1492197) baseStart_1492197 baseEnd_1492197 := by
    simpa [prefixWord, tailWord_1492197, baseEnd_1492197] using wordTrace_append hprefix tailTrace_1492197
  have hstable : (prefixWord ++ tailWord_1492197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492197).length < 2 ^ (prefixWord ++ tailWord_1492197).sum := by decide
  have hdescent : baseEnd_1492197 < baseStart_1492197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492233 : List Nat := [1, 2, 1, 1, 3, 3, 1, 1, 1, 3, 6]
def baseStart_1492233 : Nat := 118140960795 + 1492233 * 2 ^ 59
def prefixEnd_1492233 : Nat := 4983230072969 + 3 ^ 40 * 1492233 * 2
def baseEnd_1492233 : Nat := 766232777500765365224851

theorem tailTrace_1492233 : CollatzResearch.WordTrace tailWord_1492233 prefixEnd_1492233 766232777500765365224851 := by
  unfold tailWord_1492233
  simp only [CollatzResearch.WordTrace]
  refine ⟨54426208802902168951617353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36284139201934779301078235 54426208802902168951617353)
  ·
    refine ⟨40819656602176626713713015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54426208802902168951617353 40819656602176626713713015)
    ·
      refine ⟨61229484903264940070569523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40819656602176626713713015 61229484903264940070569523)
      ·
        refine ⟨91844227354897410105854285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61229484903264940070569523 91844227354897410105854285)
        ·
          refine ⟨34441585258086528789695357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91844227354897410105854285 34441585258086528789695357)
          ·
            refine ⟨12915594471782448296135759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34441585258086528789695357 12915594471782448296135759)
            ·
              refine ⟨19373391707673672444203639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12915594471782448296135759 19373391707673672444203639)
              ·
                refine ⟨29060087561510508666305459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19373391707673672444203639 29060087561510508666305459)
                ·
                  refine ⟨43590131342265762999458189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29060087561510508666305459 43590131342265762999458189)
                  ·
                    refine ⟨16346299253349661124796821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43590131342265762999458189 16346299253349661124796821)
                    ·
                      refine ⟨766232777500765365224851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16346299253349661124796821 766232777500765365224851)
                      ·
                        rfl

theorem cell23_1492233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 3, 6].length) (baseStart_1492233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1492233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1492233 prefixEnd_1492233 := by exact prefixLift 1492233
  have htrace : WordTrace (prefixWord ++ tailWord_1492233) baseStart_1492233 baseEnd_1492233 := by
    simpa [prefixWord, tailWord_1492233, baseEnd_1492233] using wordTrace_append hprefix tailTrace_1492233
  have hstable : (prefixWord ++ tailWord_1492233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492233).length < 2 ^ (prefixWord ++ tailWord_1492233).sum := by decide
  have hdescent : baseEnd_1492233 < baseStart_1492233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492247 : List Nat := [1, 1, 3, 4, 1, 1, 4, 1, 3, 4]
def baseStart_1492247 : Nat := 118140960795 + 1492247 * 2 ^ 59
def prefixEnd_1492247 : Nat := 4983230072969 + 3 ^ 40 * 1492247 * 2
def baseEnd_1492247 : Nat := 255413322076642770149929

theorem tailTrace_1492247 : CollatzResearch.WordTrace tailWord_1492247 prefixEnd_1492247 255413322076642770149929 := by
  unfold tailWord_1492247
  simp only [CollatzResearch.WordTrace]
  refine ⟨54426719424851449342626995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36284479616567632895084663 54426719424851449342626995)
  ·
    refine ⟨81640079137277174013940493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54426719424851449342626995 81640079137277174013940493)
    ·
      refine ⟨30615029676478940255227685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81640079137277174013940493 30615029676478940255227685)
      ·
        refine ⟨5740318064339801297855191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30615029676478940255227685 5740318064339801297855191)
        ·
          refine ⟨8610477096509701946782787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5740318064339801297855191 8610477096509701946782787)
          ·
            refine ⟨12915715644764552920174181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8610477096509701946782787 12915715644764552920174181)
            ·
              refine ⟨2421696683393353672532659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12915715644764552920174181 2421696683393353672532659)
              ·
                refine ⟨3632545025090030508798989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2421696683393353672532659 3632545025090030508798989)
                ·
                  refine ⟨1362204384408761440799621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3632545025090030508798989 1362204384408761440799621)
                  ·
                    refine ⟨255413322076642770149929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1362204384408761440799621 255413322076642770149929)
                    ·
                      rfl

theorem cell23_1492247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 1, 3, 4].length) (baseStart_1492247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1492247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1492247 prefixEnd_1492247 := by exact prefixLift 1492247
  have htrace : WordTrace (prefixWord ++ tailWord_1492247) baseStart_1492247 baseEnd_1492247 := by
    simpa [prefixWord, tailWord_1492247, baseEnd_1492247] using wordTrace_append hprefix tailTrace_1492247
  have hstable : (prefixWord ++ tailWord_1492247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492247).length < 2 ^ (prefixWord ++ tailWord_1492247).sum := by decide
  have hdescent : baseEnd_1492247 < baseStart_1492247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492283 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 7]
def baseStart_1492283 : Nat := 118140960795 + 1492283 * 2 ^ 59
def prefixEnd_1492283 : Nat := 4983230072969 + 3 ^ 40 * 1492283 * 2
def baseEnd_1492283 : Nat := 766258451533490169599621

theorem tailTrace_1492283 : CollatzResearch.WordTrace tailWord_1492283 prefixEnd_1492283 766258451533490169599621 := by
  unfold tailWord_1492283
  simp only [CollatzResearch.WordTrace]
  refine ⟨54428032452721027490937503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36285354968480684993958335 54428032452721027490937503)
  ·
    refine ⟨81642048679081541236406255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54428032452721027490937503 81642048679081541236406255)
    ·
      refine ⟨122463073018622311854609383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81642048679081541236406255 122463073018622311854609383)
      ·
        refine ⟨183694609527933467781914075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122463073018622311854609383 183694609527933467781914075)
        ·
          refine ⟨275541914291900201672871113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183694609527933467781914075 275541914291900201672871113)
          ·
            refine ⟨206656435718925151254653335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 275541914291900201672871113 206656435718925151254653335)
            ·
              refine ⟨309984653578387726881980003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206656435718925151254653335 309984653578387726881980003)
              ·
                refine ⟨464976980367581590322970005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 309984653578387726881980003 464976980367581590322970005)
                ·
                  refine ⟨21795795954730387046389219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 464976980367581590322970005 21795795954730387046389219)
                  ·
                    refine ⟨32693693932095580569583829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21795795954730387046389219 32693693932095580569583829)
                    ·
                      refine ⟨766258451533490169599621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 32693693932095580569583829 766258451533490169599621)
                      ·
                        rfl

theorem cell23_1492283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 7].length) (baseStart_1492283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1492283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1492283 prefixEnd_1492283 := by exact prefixLift 1492283
  have htrace : WordTrace (prefixWord ++ tailWord_1492283) baseStart_1492283 baseEnd_1492283 := by
    simpa [prefixWord, tailWord_1492283, baseEnd_1492283] using wordTrace_append hprefix tailTrace_1492283
  have hstable : (prefixWord ++ tailWord_1492283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492283).length < 2 ^ (prefixWord ++ tailWord_1492283).sum := by decide
  have hdescent : baseEnd_1492283 < baseStart_1492283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492297 : List Nat := [1, 2, 1, 1, 2, 3, 3, 1, 4, 3, 2]
def baseStart_1492297 : Nat := 118140960795 + 1492297 * 2 ^ 59
def prefixEnd_1492297 : Nat := 4983230072969 + 3 ^ 40 * 1492297 * 2
def baseEnd_1492297 : Nat := 766265640262653114824557

theorem tailTrace_1492297 : CollatzResearch.WordTrace tailWord_1492297 prefixEnd_1492297 766265640262653114824557 := by
  unfold tailWord_1492297
  simp only [CollatzResearch.WordTrace]
  refine ⟨54428543074670307881947145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36285695383113538587964763 54428543074670307881947145)
  ·
    refine ⟨40821407306002730911460359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54428543074670307881947145 40821407306002730911460359)
    ·
      refine ⟨61232110959004096367190539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40821407306002730911460359 61232110959004096367190539)
      ·
        refine ⟨91848166438506144550785809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61232110959004096367190539 91848166438506144550785809)
        ·
          refine ⟨68886124828879608413089357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91848166438506144550785809 68886124828879608413089357)
          ·
            refine ⟨25832296810829853154908509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68886124828879608413089357 25832296810829853154908509)
            ·
              refine ⟨9687111304061194933090691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25832296810829853154908509 9687111304061194933090691)
              ·
                refine ⟨14530666956091792399636037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9687111304061194933090691 14530666956091792399636037)
                ·
                  refine ⟨2724500054267211074931757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14530666956091792399636037 2724500054267211074931757)
                  ·
                    refine ⟨1021687520350204153099409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2724500054267211074931757 1021687520350204153099409)
                    ·
                      refine ⟨766265640262653114824557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1021687520350204153099409 766265640262653114824557)
                      ·
                        rfl

theorem cell23_1492297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 4, 3, 2].length) (baseStart_1492297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1492297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1492297 prefixEnd_1492297 := by exact prefixLift 1492297
  have htrace : WordTrace (prefixWord ++ tailWord_1492297) baseStart_1492297 baseEnd_1492297 := by
    simpa [prefixWord, tailWord_1492297, baseEnd_1492297] using wordTrace_append hprefix tailTrace_1492297
  have hstable : (prefixWord ++ tailWord_1492297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492297).length < 2 ^ (prefixWord ++ tailWord_1492297).sum := by decide
  have hdescent : baseEnd_1492297 < baseStart_1492297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492324 : List Nat := [2, 3, 1, 1, 3, 4, 1, 2, 1, 5]
def baseStart_1492324 : Nat := 118140960795 + 1492324 * 2 ^ 59
def prefixEnd_1492324 : Nat := 4983230072969 + 3 ^ 40 * 1492324 * 2
def baseEnd_1492324 : Nat := 255426501413441503062311

theorem tailTrace_1492324 : CollatzResearch.WordTrace tailWord_1492324 prefixEnd_1492324 255426501413441503062311 := by
  unfold tailWord_1492324
  simp only [CollatzResearch.WordTrace]
  refine ⟨27214763922786245746590013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36286351897048327662120017 27214763922786245746590013)
  ·
    refine ⟨10205536471044842154971255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27214763922786245746590013 10205536471044842154971255)
    ·
      refine ⟨15308304706567263232456883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10205536471044842154971255 15308304706567263232456883)
      ·
        refine ⟨22962457059850894848685325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15308304706567263232456883 22962457059850894848685325)
        ·
          refine ⟨8610921397444085568256997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22962457059850894848685325 8610921397444085568256997)
          ·
            refine ⟨1614547762020766044048187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8610921397444085568256997 1614547762020766044048187)
            ·
              refine ⟨2421821643031149066072281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1614547762020766044048187 2421821643031149066072281)
              ·
                refine ⟨1816366232273361799554211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2421821643031149066072281 1816366232273361799554211)
                ·
                  refine ⟨2724549348410042699331317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1816366232273361799554211 2724549348410042699331317)
                  ·
                    refine ⟨255426501413441503062311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2724549348410042699331317 255426501413441503062311)
                    ·
                      rfl

theorem cell23_1492324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 2, 1, 5].length) (baseStart_1492324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1492324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1492324 prefixEnd_1492324 := by exact prefixLift 1492324
  have htrace : WordTrace (prefixWord ++ tailWord_1492324) baseStart_1492324 baseEnd_1492324 := by
    simpa [prefixWord, tailWord_1492324, baseEnd_1492324] using wordTrace_append hprefix tailTrace_1492324
  have hstable : (prefixWord ++ tailWord_1492324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492324).length < 2 ^ (prefixWord ++ tailWord_1492324).sum := by decide
  have hdescent : baseEnd_1492324 < baseStart_1492324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492341 : List Nat := [1, 3, 4, 1, 3, 1, 3, 1, 1, 5]
def baseStart_1492341 : Nat := 118140960795 + 1492341 * 2 ^ 59
def prefixEnd_1492341 : Nat := 4983230072969 + 3 ^ 40 * 1492341 * 2
def baseEnd_1492341 : Nat := 255429411137150314224785

theorem tailTrace_1492341 : CollatzResearch.WordTrace tailWord_1492341 prefixEnd_1492341 255429411137150314224785 := by
  unfold tailWord_1492341
  simp only [CollatzResearch.WordTrace]
  refine ⟨54430147886510903396548877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36286765257673935597699251 54430147886510903396548877)
  ·
    refine ⟨20411305457441588773705829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54430147886510903396548877 20411305457441588773705829)
    ·
      refine ⟨3827119773270297895069843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20411305457441588773705829 3827119773270297895069843)
      ·
        refine ⟨5740679659905446842604765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3827119773270297895069843 5740679659905446842604765)
        ·
          refine ⟨2152754872464542565976787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5740679659905446842604765 2152754872464542565976787)
          ·
            refine ⟨3229132308696813848965181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2152754872464542565976787 3229132308696813848965181)
            ·
              refine ⟨1210924615761305193361943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3229132308696813848965181 1210924615761305193361943)
              ·
                refine ⟨1816386923641957790042915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1210924615761305193361943 1816386923641957790042915)
                ·
                  refine ⟨2724580385462936685064373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1816386923641957790042915 2724580385462936685064373)
                  ·
                    refine ⟨255429411137150314224785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2724580385462936685064373 255429411137150314224785)
                    ·
                      rfl

theorem cell23_1492341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_1492341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1492341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1492341 prefixEnd_1492341 := by exact prefixLift 1492341
  have htrace : WordTrace (prefixWord ++ tailWord_1492341) baseStart_1492341 baseEnd_1492341 := by
    simpa [prefixWord, tailWord_1492341, baseEnd_1492341] using wordTrace_append hprefix tailTrace_1492341
  have hstable : (prefixWord ++ tailWord_1492341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492341).length < 2 ^ (prefixWord ++ tailWord_1492341).sum := by decide
  have hdescent : baseEnd_1492341 < baseStart_1492341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492377 : List Nat := [1, 2, 1, 2, 1, 5, 1, 3, 1, 3, 3]
def baseStart_1492377 : Nat := 118140960795 + 1492377 * 2 ^ 59
def prefixEnd_1492377 : Nat := 4983230072969 + 3 ^ 40 * 1492377 * 2
def baseEnd_1492377 : Nat := 766306718715012801824189

theorem tailTrace_1492377 : CollatzResearch.WordTrace tailWord_1492377 prefixEnd_1492377 766306718715012801824189 := by
  unfold tailWord_1492377
  simp only [CollatzResearch.WordTrace]
  refine ⟨54431460914380481544859385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36287640609586987696572923 54431460914380481544859385)
  ·
    refine ⟨40823595685785361158644539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54431460914380481544859385 40823595685785361158644539)
    ·
      refine ⟨61235393528678041737966809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40823595685785361158644539 61235393528678041737966809)
      ·
        refine ⟨45926545146508531303475107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61235393528678041737966809 45926545146508531303475107)
        ·
          refine ⟨68889817719762796955212661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45926545146508531303475107 68889817719762796955212661)
          ·
            refine ⟨6458420411227762214551187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68889817719762796955212661 6458420411227762214551187)
            ·
              refine ⟨9687630616841643321826781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6458420411227762214551187 9687630616841643321826781)
              ·
                refine ⟨3632861481315616245685043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9687630616841643321826781 3632861481315616245685043)
                ·
                  refine ⟨5449292221973424368527565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3632861481315616245685043 5449292221973424368527565)
                  ·
                    refine ⟨2043484583240034138197837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5449292221973424368527565 2043484583240034138197837)
                    ·
                      refine ⟨766306718715012801824189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2043484583240034138197837 766306718715012801824189)
                      ·
                        rfl

theorem cell23_1492377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 3, 1, 3, 3].length) (baseStart_1492377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1492377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1492377 prefixEnd_1492377 := by exact prefixLift 1492377
  have htrace : WordTrace (prefixWord ++ tailWord_1492377) baseStart_1492377 baseEnd_1492377 := by
    simpa [prefixWord, tailWord_1492377, baseEnd_1492377] using wordTrace_append hprefix tailTrace_1492377
  have hstable : (prefixWord ++ tailWord_1492377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492377).length < 2 ^ (prefixWord ++ tailWord_1492377).sum := by decide
  have hdescent : baseEnd_1492377 < baseStart_1492377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492400 : List Nat := [2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 4]
def baseStart_1492400 : Nat := 118140960795 + 1492400 * 2 ^ 59
def prefixEnd_1492400 : Nat := 4983230072969 + 3 ^ 40 * 1492400 * 2
def baseEnd_1492400 : Nat := 766318528770066211836583

theorem tailTrace_1492400 : CollatzResearch.WordTrace tailWord_1492400 prefixEnd_1492400 766318528770066211836583 := by
  unfold tailWord_1492400
  simp only [CollatzResearch.WordTrace]
  refine ⟨27216149896648578236473327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36288199862198104315297769 27216149896648578236473327)
  ·
    refine ⟨40824224844972867354709991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27216149896648578236473327 40824224844972867354709991)
    ·
      refine ⟨61236337267459301032064987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40824224844972867354709991 61236337267459301032064987)
      ·
        refine ⟨91854505901188951548097481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61236337267459301032064987 91854505901188951548097481)
        ·
          refine ⟨68890879425891713661073111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91854505901188951548097481 68890879425891713661073111)
          ·
            refine ⟨103336319138837570491609667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68890879425891713661073111 103336319138837570491609667)
            ·
              refine ⟨155004478708256355737414501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103336319138837570491609667 155004478708256355737414501)
              ·
                refine ⟨29063339757798066700765219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 155004478708256355737414501 29063339757798066700765219)
                ·
                  refine ⟨43595009636697100051147829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29063339757798066700765219 43595009636697100051147829)
                  ·
                    refine ⟨4087032153440353129795109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43595009636697100051147829 4087032153440353129795109)
                    ·
                      refine ⟨766318528770066211836583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4087032153440353129795109 766318528770066211836583)
                      ·
                        rfl

theorem cell23_1492400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 4].length) (baseStart_1492400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1492400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1492400 prefixEnd_1492400 := by exact prefixLift 1492400
  have htrace : WordTrace (prefixWord ++ tailWord_1492400) baseStart_1492400 baseEnd_1492400 := by
    simpa [prefixWord, tailWord_1492400, baseEnd_1492400] using wordTrace_append hprefix tailTrace_1492400
  have hstable : (prefixWord ++ tailWord_1492400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492400).length < 2 ^ (prefixWord ++ tailWord_1492400).sum := by decide
  have hdescent : baseEnd_1492400 < baseStart_1492400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492428 : List Nat := [2, 2, 1, 4, 2, 2, 3, 1, 2, 1, 3]
def baseStart_1492428 : Nat := 118140960795 + 1492428 * 2 ^ 59
def prefixEnd_1492428 : Nat := 4983230072969 + 3 ^ 40 * 1492428 * 2
def baseEnd_1492428 : Nat := 766332906228392102286455

theorem tailTrace_1492428 : CollatzResearch.WordTrace tailWord_1492428 prefixEnd_1492428 766332906228392102286455 := by
  unfold tailWord_1492428
  simp only [CollatzResearch.WordTrace]
  refine ⟨27216660518597858627482969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36288880691463811503310625 27216660518597858627482969)
  ·
    refine ⟨20412495388948393970612227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27216660518597858627482969 20412495388948393970612227)
    ·
      refine ⟨30618743083422590955918341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20412495388948393970612227 30618743083422590955918341)
      ·
        refine ⟨5741014328141735804234689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30618743083422590955918341 5741014328141735804234689)
        ·
          refine ⟨4305760746106301853176017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5741014328141735804234689 4305760746106301853176017)
          ·
            refine ⟨3229320559579726389882013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4305760746106301853176017 3229320559579726389882013)
            ·
              refine ⟨1210995209842397396205755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3229320559579726389882013 1210995209842397396205755)
              ·
                refine ⟨1816492814763596094308633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1210995209842397396205755 1816492814763596094308633)
                ·
                  refine ⟨1362369611072697070731475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1816492814763596094308633 1362369611072697070731475)
                  ·
                    refine ⟨2043554416609045606097213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1362369611072697070731475 2043554416609045606097213)
                    ·
                      refine ⟨766332906228392102286455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2043554416609045606097213 766332906228392102286455)
                      ·
                        rfl

theorem cell23_1492428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 3, 1, 2, 1, 3].length) (baseStart_1492428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1492428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1492428 prefixEnd_1492428 := by exact prefixLift 1492428
  have htrace : WordTrace (prefixWord ++ tailWord_1492428) baseStart_1492428 baseEnd_1492428 := by
    simpa [prefixWord, tailWord_1492428, baseEnd_1492428] using wordTrace_append hprefix tailTrace_1492428
  have hstable : (prefixWord ++ tailWord_1492428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492428).length < 2 ^ (prefixWord ++ tailWord_1492428).sum := by decide
  have hdescent : baseEnd_1492428 < baseStart_1492428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492437 : List Nat := [1, 3, 2, 3, 1, 1, 2, 2, 2, 1, 5]
def baseStart_1492437 : Nat := 118140960795 + 1492437 * 2 ^ 59
def prefixEnd_1492437 : Nat := 4983230072969 + 3 ^ 40 * 1492437 * 2
def baseEnd_1492437 : Nat := 766337527554282567073913

theorem tailTrace_1492437 : CollatzResearch.WordTrace tailWord_1492437 prefixEnd_1492437 766337527554282567073913 := by
  unfold tailWord_1492437
  simp only [CollatzResearch.WordTrace]
  refine ⟨54433649294163111792043565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36289099529442074528029043 54433649294163111792043565)
  ·
    refine ⟨20412618485311166922016337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54433649294163111792043565 20412618485311166922016337)
    ·
      refine ⟨15309463863983375191512253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20412618485311166922016337 15309463863983375191512253)
      ·
        refine ⟨5741048948993765696817095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15309463863983375191512253 5741048948993765696817095)
        ·
          refine ⟨8611573423490648545225643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5741048948993765696817095 8611573423490648545225643)
          ·
            refine ⟨12917360135235972817838465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8611573423490648545225643 12917360135235972817838465)
            ·
              refine ⟨9688020101426979613378849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12917360135235972817838465 9688020101426979613378849)
              ·
                refine ⟨7266015076070234710034137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9688020101426979613378849 7266015076070234710034137)
                ·
                  refine ⟨5449511307052676032525603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7266015076070234710034137 5449511307052676032525603)
                  ·
                    refine ⟨8174266960579014048788405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5449511307052676032525603 8174266960579014048788405)
                    ·
                      refine ⟨766337527554282567073913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8174266960579014048788405 766337527554282567073913)
                      ·
                        rfl

theorem cell23_1492437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_1492437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1492437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1492437 prefixEnd_1492437 := by exact prefixLift 1492437
  have htrace : WordTrace (prefixWord ++ tailWord_1492437) baseStart_1492437 baseEnd_1492437 := by
    simpa [prefixWord, tailWord_1492437, baseEnd_1492437] using wordTrace_append hprefix tailTrace_1492437
  have hstable : (prefixWord ++ tailWord_1492437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492437).length < 2 ^ (prefixWord ++ tailWord_1492437).sum := by decide
  have hdescent : baseEnd_1492437 < baseStart_1492437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492438 : List Nat := [5, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2]
def baseStart_1492438 : Nat := 118140960795 + 1492438 * 2 ^ 59
def prefixEnd_1492438 : Nat := 4983230072969 + 3 ^ 40 * 1492438 * 2
def baseEnd_1492438 : Nat := 766338041034937063161409

theorem tailTrace_1492438 : CollatzResearch.WordTrace tailWord_1492438 prefixEnd_1492438 766338041034937063161409 := by
  unfold tailWord_1492438
  simp only [CollatzResearch.WordTrace]
  refine ⟨3402105360447468060176873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36289123844772992641886645 3402105360447468060176873)
  ·
    refine ⟨2551579020335601045132655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3402105360447468060176873 2551579020335601045132655)
    ·
      refine ⟨3827368530503401567698983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2551579020335601045132655 3827368530503401567698983)
      ·
        refine ⟨5741052795755102351548475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3827368530503401567698983 5741052795755102351548475)
        ·
          refine ⟨8611579193632653527322713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5741052795755102351548475 8611579193632653527322713)
          ·
            refine ⟨6458684395224490145492035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8611579193632653527322713 6458684395224490145492035)
            ·
              refine ⟨9688026592836735218238053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6458684395224490145492035 9688026592836735218238053)
              ·
                refine ⟨1816504986156887853419635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9688026592836735218238053 1816504986156887853419635)
                ·
                  refine ⟨2724757479235331780129453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1816504986156887853419635 2724757479235331780129453)
                  ·
                    refine ⟨1021784054713249417548545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2724757479235331780129453 1021784054713249417548545)
                    ·
                      refine ⟨766338041034937063161409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1021784054713249417548545 766338041034937063161409)
                      ·
                        rfl

theorem cell23_1492438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2].length) (baseStart_1492438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1492438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1492438 prefixEnd_1492438 := by exact prefixLift 1492438
  have htrace : WordTrace (prefixWord ++ tailWord_1492438) baseStart_1492438 baseEnd_1492438 := by
    simpa [prefixWord, tailWord_1492438, baseEnd_1492438] using wordTrace_append hprefix tailTrace_1492438
  have hstable : (prefixWord ++ tailWord_1492438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492438).length < 2 ^ (prefixWord ++ tailWord_1492438).sum := by decide
  have hdescent : baseEnd_1492438 < baseStart_1492438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492451 : List Nat := [1, 1, 1, 6, 2, 1, 1, 2, 4, 2, 2]
def baseStart_1492451 : Nat := 118140960795 + 1492451 * 2 ^ 59
def prefixEnd_1492451 : Nat := 4983230072969 + 3 ^ 40 * 1492451 * 2
def baseEnd_1492451 : Nat := 766344716283445512298849

theorem tailTrace_1492451 : CollatzResearch.WordTrace tailWord_1492451 prefixEnd_1492451 766344716283445512298849 := by
  unfold tailWord_1492451
  simp only [CollatzResearch.WordTrace]
  refine ⟨54434159916112392183053207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36289439944074928122035471 54434159916112392183053207)
  ·
    refine ⟨81651239874168588274579811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54434159916112392183053207 81651239874168588274579811)
    ·
      refine ⟨122476859811252882411869717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81651239874168588274579811 122476859811252882411869717)
      ·
        refine ⟨5741102803652478863056393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 122476859811252882411869717 5741102803652478863056393)
        ·
          refine ⟨4305827102739359147292295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5741102803652478863056393 4305827102739359147292295)
          ·
            refine ⟨6458740654109038720938443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4305827102739359147292295 6458740654109038720938443)
            ·
              refine ⟨9688110981163558081407665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6458740654109038720938443 9688110981163558081407665)
              ·
                refine ⟨7266083235872668561055749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9688110981163558081407665 7266083235872668561055749)
                ·
                  refine ⟨1362390606726125355197953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7266083235872668561055749 1362390606726125355197953)
                  ·
                    refine ⟨1021792955044594016398465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1362390606726125355197953 1021792955044594016398465)
                    ·
                      refine ⟨766344716283445512298849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1021792955044594016398465 766344716283445512298849)
                      ·
                        rfl

theorem cell23_1492451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 4, 2, 2].length) (baseStart_1492451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1492451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1492451 prefixEnd_1492451 := by exact prefixLift 1492451
  have htrace : WordTrace (prefixWord ++ tailWord_1492451) baseStart_1492451 baseEnd_1492451 := by
    simpa [prefixWord, tailWord_1492451, baseEnd_1492451] using wordTrace_append hprefix tailTrace_1492451
  have hstable : (prefixWord ++ tailWord_1492451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492451).length < 2 ^ (prefixWord ++ tailWord_1492451).sum := by decide
  have hdescent : baseEnd_1492451 < baseStart_1492451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492467 : List Nat := [1, 1, 1, 2, 2, 2, 2, 4, 2, 3, 3]
def baseStart_1492467 : Nat := 118140960795 + 1492467 * 2 ^ 59
def prefixEnd_1492467 : Nat := 4983230072969 + 3 ^ 40 * 1492467 * 2
def baseEnd_1492467 : Nat := 766352931973917449698775

theorem tailTrace_1492467 : CollatzResearch.WordTrace tailWord_1492467 prefixEnd_1492467 766352931973917449698775 := by
  unfold tailWord_1492467
  simp only [CollatzResearch.WordTrace]
  refine ⟨54434743484054426915635655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36289828989369617943757103 54434743484054426915635655)
  ·
    refine ⟨81652115226081640373453483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54434743484054426915635655 81652115226081640373453483)
    ·
      refine ⟨122478172839122460560180225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81652115226081640373453483 122478172839122460560180225)
      ·
        refine ⟨91858629629341845420135169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122478172839122460560180225 91858629629341845420135169)
        ·
          refine ⟨68893972222006384065101377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91858629629341845420135169 68893972222006384065101377)
          ·
            refine ⟨51670479166504788048826033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68893972222006384065101377 51670479166504788048826033)
            ·
              refine ⟨38752859374878591036619525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51670479166504788048826033 38752859374878591036619525)
              ·
                refine ⟨7266161132789735819366161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38752859374878591036619525 7266161132789735819366161)
                ·
                  refine ⟨5449620849592301864524621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7266161132789735819366161 5449620849592301864524621)
                  ·
                    refine ⟨2043607818597113199196733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5449620849592301864524621 2043607818597113199196733)
                    ·
                      refine ⟨766352931973917449698775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2043607818597113199196733 766352931973917449698775)
                      ·
                        rfl

theorem cell23_1492467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 2, 3, 3].length) (baseStart_1492467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1492467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1492467 prefixEnd_1492467 := by exact prefixLift 1492467
  have htrace : WordTrace (prefixWord ++ tailWord_1492467) baseStart_1492467 baseEnd_1492467 := by
    simpa [prefixWord, tailWord_1492467, baseEnd_1492467] using wordTrace_append hprefix tailTrace_1492467
  have hstable : (prefixWord ++ tailWord_1492467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492467).length < 2 ^ (prefixWord ++ tailWord_1492467).sum := by decide
  have hdescent : baseEnd_1492467 < baseStart_1492467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492551 : List Nat := [1, 1, 4, 1, 5, 1, 1, 2, 3, 4]
def baseStart_1492551 : Nat := 118140960795 + 1492551 * 2 ^ 59
def prefixEnd_1492551 : Nat := 4983230072969 + 3 ^ 40 * 1492551 * 2
def baseEnd_1492551 : Nat := 255465354782965040349463

theorem tailTrace_1492551 : CollatzResearch.WordTrace tailWord_1492551 prefixEnd_1492551 255465354782965040349463 := by
  unfold tailWord_1492551
  simp only [CollatzResearch.WordTrace]
  refine ⟨54437807215750109261693507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36291871477166739507795671 54437807215750109261693507)
  ·
    refine ⟨81656710823625163892540261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54437807215750109261693507 81656710823625163892540261)
    ·
      refine ⟨15310633279429718229851299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81656710823625163892540261 15310633279429718229851299)
      ·
        refine ⟨22965949919144577344776949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15310633279429718229851299 22965949919144577344776949)
        ·
          refine ⟨2153057804919804126072839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22965949919144577344776949 2153057804919804126072839)
          ·
            refine ⟨3229586707379706189109259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2153057804919804126072839 3229586707379706189109259)
            ·
              refine ⟨4844380061069559283663889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3229586707379706189109259 4844380061069559283663889)
              ·
                refine ⟨3633285045802169462747917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4844380061069559283663889 3633285045802169462747917)
                ·
                  refine ⟨1362481892175813548530469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3633285045802169462747917 1362481892175813548530469)
                  ·
                    refine ⟨255465354782965040349463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1362481892175813548530469 255465354782965040349463)
                    ·
                      rfl

theorem cell23_1492551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 2, 3, 4].length) (baseStart_1492551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1492551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1492551 prefixEnd_1492551 := by exact prefixLift 1492551
  have htrace : WordTrace (prefixWord ++ tailWord_1492551) baseStart_1492551 baseEnd_1492551 := by
    simpa [prefixWord, tailWord_1492551, baseEnd_1492551] using wordTrace_append hprefix tailTrace_1492551
  have hstable : (prefixWord ++ tailWord_1492551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492551).length < 2 ^ (prefixWord ++ tailWord_1492551).sum := by decide
  have hdescent : baseEnd_1492551 < baseStart_1492551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492581 : List Nat := [1, 3, 1, 3, 3, 3, 1, 2, 6]
def baseStart_1492581 : Nat := 118140960795 + 1492581 * 2 ^ 59
def prefixEnd_1492581 : Nat := 4983230072969 + 3 ^ 40 * 1492581 * 2
def baseEnd_1492581 : Nat := 85156829863170000408139

theorem tailTrace_1492581 : CollatzResearch.WordTrace tailWord_1492581 prefixEnd_1492581 85156829863170000408139 := by
  unfold tailWord_1492581
  simp only [CollatzResearch.WordTrace]
  refine ⟨54438901405641424385285597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36292600937094282923523731 54438901405641424385285597)
  ·
    refine ⟨20414588027115534144482099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54438901405641424385285597 20414588027115534144482099)
    ·
      refine ⟨30621882040673301216723149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20414588027115534144482099 30621882040673301216723149)
      ·
        refine ⟨11483205765252487956271181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30621882040673301216723149 11483205765252487956271181)
        ·
          refine ⟨4306202161969682983601693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11483205765252487956271181 4306202161969682983601693)
          ·
            refine ⟨1614825810738631118850635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4306202161969682983601693 1614825810738631118850635)
            ·
              refine ⟨2422238716107946678275953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1614825810738631118850635 2422238716107946678275953)
              ·
                refine ⟨1816679037080960008706965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2422238716107946678275953 1816679037080960008706965)
                ·
                  refine ⟨85156829863170000408139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1816679037080960008706965 85156829863170000408139)
                  ·
                    rfl

theorem cell23_1492581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 2, 6].length) (baseStart_1492581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1492581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1492581 prefixEnd_1492581 := by exact prefixLift 1492581
  have htrace : WordTrace (prefixWord ++ tailWord_1492581) baseStart_1492581 baseEnd_1492581 := by
    simpa [prefixWord, tailWord_1492581, baseEnd_1492581] using wordTrace_append hprefix tailTrace_1492581
  have hstable : (prefixWord ++ tailWord_1492581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492581).length < 2 ^ (prefixWord ++ tailWord_1492581).sum := by decide
  have hdescent : baseEnd_1492581 < baseStart_1492581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492584 : List Nat := [2, 1, 4, 3, 1, 1, 1, 1, 1, 2, 6]
def baseStart_1492584 : Nat := 118140960795 + 1492584 * 2 ^ 59
def prefixEnd_1492584 : Nat := 4983230072969 + 3 ^ 40 * 1492584 * 2
def baseEnd_1492584 : Nat := 766413009210493491935737

theorem tailTrace_1492584 : CollatzResearch.WordTrace tailWord_1492584 prefixEnd_1492584 766413009210493491935737 := by
  unfold tailWord_1492584
  simp only [CollatzResearch.WordTrace]
  refine ⟨27219505412315277948822403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36292673883087037265096537 27219505412315277948822403)
  ·
    refine ⟨40829258118472916923233605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27219505412315277948822403 40829258118472916923233605)
    ·
      refine ⟨7655485897213671923106301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40829258118472916923233605 7655485897213671923106301)
      ·
        refine ⟨2870807211455126971164863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7655485897213671923106301 2870807211455126971164863)
        ·
          refine ⟨4306210817182690456747295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2870807211455126971164863 4306210817182690456747295)
          ·
            refine ⟨6459316225774035685120943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4306210817182690456747295 6459316225774035685120943)
            ·
              refine ⟨9688974338661053527681415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6459316225774035685120943 9688974338661053527681415)
              ·
                refine ⟨14533461507991580291522123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9688974338661053527681415 14533461507991580291522123)
                ·
                  refine ⟨21800192261987370437283185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14533461507991580291522123 21800192261987370437283185)
                  ·
                    refine ⟨16350144196490527827962389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21800192261987370437283185 16350144196490527827962389)
                    ·
                      refine ⟨766413009210493491935737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16350144196490527827962389 766413009210493491935737)
                      ·
                        rfl

theorem cell23_1492584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_1492584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1492584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1492584 prefixEnd_1492584 := by exact prefixLift 1492584
  have htrace : WordTrace (prefixWord ++ tailWord_1492584) baseStart_1492584 baseEnd_1492584 := by
    simpa [prefixWord, tailWord_1492584, baseEnd_1492584] using wordTrace_append hprefix tailTrace_1492584
  have hstable : (prefixWord ++ tailWord_1492584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492584).length < 2 ^ (prefixWord ++ tailWord_1492584).sum := by decide
  have hdescent : baseEnd_1492584 < baseStart_1492584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492598 : List Nat := [5, 1, 1, 2, 2, 2, 3, 1, 6]
def baseStart_1492598 : Nat := 118140960795 + 1492598 * 2 ^ 59
def prefixEnd_1492598 : Nat := 4983230072969 + 3 ^ 40 * 1492598 * 2
def baseEnd_1492598 : Nat := 85157799771072937462297

theorem tailTrace_1492598 : CollatzResearch.WordTrace tailWord_1492598 prefixEnd_1492598 85157799771072937462297 := by
  unfold tailWord_1492598
  simp only [CollatzResearch.WordTrace]
  refine ⟨3402470090411239768040903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36293014297719890859102965 3402470090411239768040903)
  ·
    refine ⟨5103705135616859652061355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3402470090411239768040903 5103705135616859652061355)
    ·
      refine ⟨7655557703425289478092033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5103705135616859652061355 7655557703425289478092033)
      ·
        refine ⟨5741668277568967108569025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7655557703425289478092033 5741668277568967108569025)
        ·
          refine ⟨4306251208176725331426769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5741668277568967108569025 4306251208176725331426769)
          ·
            refine ⟨3229688406132543998570077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4306251208176725331426769 3229688406132543998570077)
            ·
              refine ⟨1211133152299703999463779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3229688406132543998570077 1211133152299703999463779)
              ·
                refine ⟨1816699728449555999195669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1211133152299703999463779 1816699728449555999195669)
                ·
                  refine ⟨85157799771072937462297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1816699728449555999195669 85157799771072937462297)
                  ·
                    rfl

theorem cell23_1492598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 3, 1, 6].length) (baseStart_1492598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1492598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1492598 prefixEnd_1492598 := by exact prefixLift 1492598
  have htrace : WordTrace (prefixWord ++ tailWord_1492598) baseStart_1492598 baseEnd_1492598 := by
    simpa [prefixWord, tailWord_1492598, baseEnd_1492598] using wordTrace_append hprefix tailTrace_1492598
  have hstable : (prefixWord ++ tailWord_1492598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492598).length < 2 ^ (prefixWord ++ tailWord_1492598).sum := by decide
  have hdescent : baseEnd_1492598 < baseStart_1492598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492627 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 6]
def baseStart_1492627 : Nat := 118140960795 + 1492627 * 2 ^ 59
def prefixEnd_1492627 : Nat := 4983230072969 + 3 ^ 40 * 1492627 * 2
def baseEnd_1492627 : Nat := 766435088878636823698039

theorem tailTrace_1492627 : CollatzResearch.WordTrace tailWord_1492627 prefixEnd_1492627 766435088878636823698039 := by
  unfold tailWord_1492627
  simp only [CollatzResearch.WordTrace]
  refine ⟨54440579163474774241460135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36293719442316516160973423 54440579163474774241460135)
  ·
    refine ⟨81660868745212161362190203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54440579163474774241460135 81660868745212161362190203)
    ·
      refine ⟨122491303117818242043285305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81660868745212161362190203 122491303117818242043285305)
      ·
        refine ⟨91868477338363681532463979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122491303117818242043285305 91868477338363681532463979)
        ·
          refine ⟨137802716007545522298695969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91868477338363681532463979 137802716007545522298695969)
          ·
            refine ⟨103352037005659141724021977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137802716007545522298695969 103352037005659141724021977)
            ·
              refine ⟨77514027754244356293016483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103352037005659141724021977 77514027754244356293016483)
              ·
                refine ⟨116271041631366534439524725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77514027754244356293016483 116271041631366534439524725)
                ·
                  refine ⟨10900410152940612603705443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 116271041631366534439524725 10900410152940612603705443)
                  ·
                    refine ⟨16350615229410918905558165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10900410152940612603705443 16350615229410918905558165)
                    ·
                      refine ⟨766435088878636823698039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16350615229410918905558165 766435088878636823698039)
                      ·
                        rfl

theorem cell23_1492627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 6].length) (baseStart_1492627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1492627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1492627 prefixEnd_1492627 := by exact prefixLift 1492627
  have htrace : WordTrace (prefixWord ++ tailWord_1492627) baseStart_1492627 baseEnd_1492627 := by
    simpa [prefixWord, tailWord_1492627, baseEnd_1492627] using wordTrace_append hprefix tailTrace_1492627
  have hstable : (prefixWord ++ tailWord_1492627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492627).length < 2 ^ (prefixWord ++ tailWord_1492627).sum := by decide
  have hdescent : baseEnd_1492627 < baseStart_1492627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492631 : List Nat := [1, 1, 3, 3, 2, 2, 2, 3, 1, 1, 4]
def baseStart_1492631 : Nat := 118140960795 + 1492631 * 2 ^ 59
def prefixEnd_1492631 : Nat := 4983230072969 + 3 ^ 40 * 1492631 * 2
def baseEnd_1492631 : Nat := 766437142801254808048021

theorem tailTrace_1492631 : CollatzResearch.WordTrace tailWord_1492631 prefixEnd_1492631 766437142801254808048021 := by
  unfold tailWord_1492631
  simp only [CollatzResearch.WordTrace]
  refine ⟨54440725055460282924605747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36293816703640188616403831 54440725055460282924605747)
  ·
    refine ⟨81661087583190424386908621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54440725055460282924605747 81661087583190424386908621)
    ·
      refine ⟨30622907843696409145090733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81661087583190424386908621 30622907843696409145090733)
      ·
        refine ⟨11483590441386153429409025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30622907843696409145090733 11483590441386153429409025)
        ·
          refine ⟨8612692831039615072056769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11483590441386153429409025 8612692831039615072056769)
          ·
            refine ⟨6459519623279711304042577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8612692831039615072056769 6459519623279711304042577)
            ·
              refine ⟨4844639717459783478031933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6459519623279711304042577 4844639717459783478031933)
              ·
                refine ⟨1816739894047418804261975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4844639717459783478031933 1816739894047418804261975)
                ·
                  refine ⟨2725109841071128206392963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1816739894047418804261975 2725109841071128206392963)
                  ·
                    refine ⟨4087664761606692309589445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2725109841071128206392963 4087664761606692309589445)
                    ·
                      refine ⟨766437142801254808048021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4087664761606692309589445 766437142801254808048021)
                      ·
                        rfl

theorem cell23_1492631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 3, 1, 1, 4].length) (baseStart_1492631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1492631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1492631 prefixEnd_1492631 := by exact prefixLift 1492631
  have htrace : WordTrace (prefixWord ++ tailWord_1492631) baseStart_1492631 baseEnd_1492631 := by
    simpa [prefixWord, tailWord_1492631, baseEnd_1492631] using wordTrace_append hprefix tailTrace_1492631
  have hstable : (prefixWord ++ tailWord_1492631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492631).length < 2 ^ (prefixWord ++ tailWord_1492631).sum := by decide
  have hdescent : baseEnd_1492631 < baseStart_1492631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492641 : List Nat := [1, 2, 3, 3, 2, 1, 2, 1, 4, 4]
def baseStart_1492641 : Nat := 118140960795 + 1492641 * 2 ^ 59
def prefixEnd_1492641 : Nat := 4983230072969 + 3 ^ 40 * 1492641 * 2
def baseEnd_1492641 : Nat := 255480759202599922974325

theorem tailTrace_1492641 : CollatzResearch.WordTrace tailWord_1492641 prefixEnd_1492641 255480759202599922974325 := by
  unfold tailWord_1492641
  simp only [CollatzResearch.WordTrace]
  refine ⟨54441089785424054632469777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36294059856949369754979851 54441089785424054632469777)
  ·
    refine ⟨40830817339068040974352333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54441089785424054632469777 40830817339068040974352333)
    ·
      refine ⟨15311556502150515365382125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40830817339068040974352333 15311556502150515365382125)
      ·
        refine ⟨5741833688306443262018297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15311556502150515365382125 5741833688306443262018297)
        ·
          refine ⟨4306375266229832446513723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5741833688306443262018297 4306375266229832446513723)
          ·
            refine ⟨6459562899344748669770585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4306375266229832446513723 6459562899344748669770585)
            ·
              refine ⟨4844672174508561502327939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6459562899344748669770585 4844672174508561502327939)
              ·
                refine ⟨7267008261762842253491909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4844672174508561502327939 7267008261762842253491909)
                ·
                  refine ⟨1362564049080532922529733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7267008261762842253491909 1362564049080532922529733)
                  ·
                    refine ⟨255480759202599922974325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1362564049080532922529733 255480759202599922974325)
                    ·
                      rfl

theorem cell23_1492641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 4, 4].length) (baseStart_1492641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1492641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1492641 prefixEnd_1492641 := by exact prefixLift 1492641
  have htrace : WordTrace (prefixWord ++ tailWord_1492641) baseStart_1492641 baseEnd_1492641 := by
    simpa [prefixWord, tailWord_1492641, baseEnd_1492641] using wordTrace_append hprefix tailTrace_1492641
  have hstable : (prefixWord ++ tailWord_1492641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492641).length < 2 ^ (prefixWord ++ tailWord_1492641).sum := by decide
  have hdescent : baseEnd_1492641 < baseStart_1492641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492642 : List Nat := [3, 3, 1, 4, 1, 2, 1, 1, 3, 1, 3]
def baseStart_1492642 : Nat := 118140960795 + 1492642 * 2 ^ 59
def prefixEnd_1492642 : Nat := 4983230072969 + 3 ^ 40 * 1492642 * 2
def baseEnd_1492642 : Nat := 766442791088454265010471

theorem tailTrace_1492642 : CollatzResearch.WordTrace tailWord_1492642 prefixEnd_1492642 766442791088454265010471 := by
  unfold tailWord_1492642
  simp only [CollatzResearch.WordTrace]
  refine ⟨13610281564605107950814045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36294084172280287868837453 13610281564605107950814045)
  ·
    refine ⟨5103855586726915481555267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13610281564605107950814045 5103855586726915481555267)
    ·
      refine ⟨7655783380090373222332901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5103855586726915481555267 7655783380090373222332901)
      ·
        refine ⟨1435459383766944979187419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7655783380090373222332901 1435459383766944979187419)
        ·
          refine ⟨2153189075650417468781129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1435459383766944979187419 2153189075650417468781129)
          ·
            refine ⟨1614891806737813101585847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2153189075650417468781129 1614891806737813101585847)
            ·
              refine ⟨2422337710106719652378771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1614891806737813101585847 2422337710106719652378771)
              ·
                refine ⟨3633506565160079478568157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2422337710106719652378771 3633506565160079478568157)
                ·
                  refine ⟨1362564961935029804463059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3633506565160079478568157 1362564961935029804463059)
                  ·
                    refine ⟨2043847442902544706694589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1362564961935029804463059 2043847442902544706694589)
                    ·
                      refine ⟨766442791088454265010471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2043847442902544706694589 766442791088454265010471)
                      ·
                        rfl

theorem cell23_1492642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_1492642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1492642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1492642 prefixEnd_1492642 := by exact prefixLift 1492642
  have htrace : WordTrace (prefixWord ++ tailWord_1492642) baseStart_1492642 baseEnd_1492642 := by
    simpa [prefixWord, tailWord_1492642, baseEnd_1492642] using wordTrace_append hprefix tailTrace_1492642
  have hstable : (prefixWord ++ tailWord_1492642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492642).length < 2 ^ (prefixWord ++ tailWord_1492642).sum := by decide
  have hdescent : baseEnd_1492642 < baseStart_1492642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492644 : List Nat := [2, 3, 1, 2, 2, 2, 1, 2, 1, 1, 6]
def baseStart_1492644 : Nat := 118140960795 + 1492644 * 2 ^ 59
def prefixEnd_1492644 : Nat := 4983230072969 + 3 ^ 40 * 1492644 * 2
def baseEnd_1492644 : Nat := 766443818049763257185461

theorem tailTrace_1492644 : CollatzResearch.WordTrace tailWord_1492644 prefixEnd_1492644 766443818049763257185461 := by
  unfold tailWord_1492644
  simp only [CollatzResearch.WordTrace]
  refine ⟨27220599602206593072414493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36294132802942124096552657 27220599602206593072414493)
  ·
    refine ⟨10207724850827472402155435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27220599602206593072414493 10207724850827472402155435)
    ·
      refine ⟨15311587276241208603233153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10207724850827472402155435 15311587276241208603233153)
      ·
        refine ⟨11483690457180906452424865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15311587276241208603233153 11483690457180906452424865)
        ·
          refine ⟨8612767842885679839318649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11483690457180906452424865 8612767842885679839318649)
          ·
            refine ⟨6459575882164259879488987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8612767842885679839318649 6459575882164259879488987)
            ·
              refine ⟨9689363823246389819233481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6459575882164259879488987 9689363823246389819233481)
              ·
                refine ⟨7267022867434792364425111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9689363823246389819233481 7267022867434792364425111)
                ·
                  refine ⟨10900534301152188546637667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7267022867434792364425111 10900534301152188546637667)
                  ·
                    refine ⟨16350801451728282819956501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10900534301152188546637667 16350801451728282819956501)
                    ·
                      refine ⟨766443818049763257185461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16350801451728282819956501 766443818049763257185461)
                      ·
                        rfl

theorem cell23_1492644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_1492644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1492644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1492644 prefixEnd_1492644 := by exact prefixLift 1492644
  have htrace : WordTrace (prefixWord ++ tailWord_1492644) baseStart_1492644 baseEnd_1492644 := by
    simpa [prefixWord, tailWord_1492644, baseEnd_1492644] using wordTrace_append hprefix tailTrace_1492644
  have hstable : (prefixWord ++ tailWord_1492644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492644).length < 2 ^ (prefixWord ++ tailWord_1492644).sum := by decide
  have hdescent : baseEnd_1492644 < baseStart_1492644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492658 : List Nat := [3, 2, 1, 1, 1, 2, 6, 1, 2, 4]
def baseStart_1492658 : Nat := 118140960795 + 1492658 * 2 ^ 59
def prefixEnd_1492658 : Nat := 4983230072969 + 3 ^ 40 * 1492658 * 2
def baseEnd_1492658 : Nat := 255483668926308734136799

theorem tailTrace_1492658 : CollatzResearch.WordTrace tailWord_1492658 prefixEnd_1492658 255483668926308734136799 := by
  unfold tailWord_1492658
  simp only [CollatzResearch.WordTrace]
  refine ⟨13610427456590616633959657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36294473217574977690559085 13610427456590616633959657)
  ·
    refine ⟨10207820592442962475469743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13610427456590616633959657 10207820592442962475469743)
    ·
      refine ⟨15311730888664443713204615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10207820592442962475469743 15311730888664443713204615)
      ·
        refine ⟨22967596332996665569806923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15311730888664443713204615 22967596332996665569806923)
        ·
          refine ⟨34451394499494998354710385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22967596332996665569806923 34451394499494998354710385)
          ·
            refine ⟨25838545874621248766032789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34451394499494998354710385 25838545874621248766032789)
            ·
              refine ⟨1211181837872871035907787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 25838545874621248766032789 1211181837872871035907787)
              ·
                refine ⟨1816772756809306553861681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1211181837872871035907787 1816772756809306553861681)
                ·
                  refine ⟨1362579567606979915396261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1816772756809306553861681 1362579567606979915396261)
                  ·
                    refine ⟨255483668926308734136799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1362579567606979915396261 255483668926308734136799)
                    ·
                      rfl

theorem cell23_1492658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 6, 1, 2, 4].length) (baseStart_1492658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1492658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1492658 prefixEnd_1492658 := by exact prefixLift 1492658
  have htrace : WordTrace (prefixWord ++ tailWord_1492658) baseStart_1492658 baseEnd_1492658 := by
    simpa [prefixWord, tailWord_1492658, baseEnd_1492658] using wordTrace_append hprefix tailTrace_1492658
  have hstable : (prefixWord ++ tailWord_1492658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492658).length < 2 ^ (prefixWord ++ tailWord_1492658).sum := by decide
  have hdescent : baseEnd_1492658 < baseStart_1492658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492664 : List Nat := [2, 1, 2, 1, 2, 1, 1, 2, 5, 3, 3]
def baseStart_1492664 : Nat := 118140960795 + 1492664 * 2 ^ 59
def prefixEnd_1492664 : Nat := 4983230072969 + 3 ^ 40 * 1492664 * 2
def baseEnd_1492664 : Nat := 766454087662853178935369

theorem tailTrace_1492664 : CollatzResearch.WordTrace tailWord_1492664 prefixEnd_1492664 766454087662853178935369 := by
  unfold tailWord_1492664
  simp only [CollatzResearch.WordTrace]
  refine ⟨27220964332170364780278523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36294619109560486373704697 27220964332170364780278523)
  ·
    refine ⟨40831446498255547170417785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27220964332170364780278523 40831446498255547170417785)
    ·
      refine ⟨30623584873691660377813339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40831446498255547170417785 30623584873691660377813339)
      ·
        refine ⟨45935377310537490566720009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30623584873691660377813339 45935377310537490566720009)
        ·
          refine ⟨34451532982903117925040007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45935377310537490566720009 34451532982903117925040007)
          ·
            refine ⟨51677299474354676887560011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34451532982903117925040007 51677299474354676887560011)
            ·
              refine ⟨77515949211532015331340017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51677299474354676887560011 77515949211532015331340017)
              ·
                refine ⟨58136961908649011498505013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77515949211532015331340017 58136961908649011498505013)
                ·
                  refine ⟨5450340178935844827984845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58136961908649011498505013 5450340178935844827984845)
                  ·
                    refine ⟨2043877567100941810494317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5450340178935844827984845 2043877567100941810494317)
                    ·
                      refine ⟨766454087662853178935369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2043877567100941810494317 766454087662853178935369)
                      ·
                        rfl

theorem cell23_1492664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 5, 3, 3].length) (baseStart_1492664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1492664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1492664 prefixEnd_1492664 := by exact prefixLift 1492664
  have htrace : WordTrace (prefixWord ++ tailWord_1492664) baseStart_1492664 baseEnd_1492664 := by
    simpa [prefixWord, tailWord_1492664, baseEnd_1492664] using wordTrace_append hprefix tailTrace_1492664
  have hstable : (prefixWord ++ tailWord_1492664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492664).length < 2 ^ (prefixWord ++ tailWord_1492664).sum := by decide
  have hdescent : baseEnd_1492664 < baseStart_1492664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492668 : List Nat := [2, 2, 2, 3, 1, 2, 3, 2, 1, 2, 3]
def baseStart_1492668 : Nat := 118140960795 + 1492668 * 2 ^ 59
def prefixEnd_1492668 : Nat := 4983230072969 + 3 ^ 40 * 1492668 * 2
def baseEnd_1492668 : Nat := 766456141585471163285351

theorem tailTrace_1492668 : CollatzResearch.WordTrace tailWord_1492668 prefixEnd_1492668 766456141585471163285351 := by
  unfold tailWord_1492668
  simp only [CollatzResearch.WordTrace]
  refine ⟨27221037278163119121851329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36294716370884158829135105 27221037278163119121851329)
  ·
    refine ⟨20415777958622339341388497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27221037278163119121851329 20415777958622339341388497)
    ·
      refine ⟨15311833468966754506041373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20415777958622339341388497 15311833468966754506041373)
      ·
        refine ⟨5741937550862532939765515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15311833468966754506041373 5741937550862532939765515)
        ·
          refine ⟨8612906326293799409648273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5741937550862532939765515 8612906326293799409648273)
          ·
            refine ⟨6459679744720349557236205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8612906326293799409648273 6459679744720349557236205)
            ·
              refine ⟨2422379904270131083963577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6459679744720349557236205 2422379904270131083963577)
              ·
                refine ⟨1816784928202598312972683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2422379904270131083963577 1816784928202598312972683)
                ·
                  refine ⟨2725177392303897469459025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1816784928202598312972683 2725177392303897469459025)
                  ·
                    refine ⟨2043883044227923102094269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2725177392303897469459025 2043883044227923102094269)
                    ·
                      refine ⟨766456141585471163285351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2043883044227923102094269 766456141585471163285351)
                      ·
                        rfl

theorem cell23_1492668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_1492668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1492668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1492668 prefixEnd_1492668 := by exact prefixLift 1492668
  have htrace : WordTrace (prefixWord ++ tailWord_1492668) baseStart_1492668 baseEnd_1492668 := by
    simpa [prefixWord, tailWord_1492668, baseEnd_1492668] using wordTrace_append hprefix tailTrace_1492668
  have hstable : (prefixWord ++ tailWord_1492668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492668).length < 2 ^ (prefixWord ++ tailWord_1492668).sum := by decide
  have hdescent : baseEnd_1492668 < baseStart_1492668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492685 : List Nat := [1, 6, 2, 1, 1, 3, 1, 1, 1, 1, 5]
def baseStart_1492685 : Nat := 118140960795 + 1492685 * 2 ^ 59
def prefixEnd_1492685 : Nat := 4983230072969 + 3 ^ 40 * 1492685 * 2
def baseEnd_1492685 : Nat := 766464870756597596772773

theorem tailTrace_1492685 : CollatzResearch.WordTrace tailWord_1492685 prefixEnd_1492685 766464870756597596772773 := by
  unfold tailWord_1492685
  simp only [CollatzResearch.WordTrace]
  refine ⟨54442694597264650147071509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36295129731509766764714339 54442694597264650147071509)
  ·
    refine ⟨2552001309246780475643977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 54442694597264650147071509 2552001309246780475643977)
    ·
      refine ⟨1914000981935085356732983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2552001309246780475643977 1914000981935085356732983)
      ·
        refine ⟨2871001472902628035099475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1914000981935085356732983 2871001472902628035099475)
        ·
          refine ⟨4306502209353942052649213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2871001472902628035099475 4306502209353942052649213)
          ·
            refine ⟨1614938328507728269743455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4306502209353942052649213 1614938328507728269743455)
            ·
              refine ⟨2422407492761592404615183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1614938328507728269743455 2422407492761592404615183)
              ·
                refine ⟨3633611239142388606922775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2422407492761592404615183 3633611239142388606922775)
                ·
                  refine ⟨5450416858713582910384163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3633611239142388606922775 5450416858713582910384163)
                  ·
                    refine ⟨8175625288070374365576245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5450416858713582910384163 8175625288070374365576245)
                    ·
                      refine ⟨766464870756597596772773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8175625288070374365576245 766464870756597596772773)
                      ·
                        rfl

theorem cell23_1492685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_1492685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1492685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1492685 prefixEnd_1492685 := by exact prefixLift 1492685
  have htrace : WordTrace (prefixWord ++ tailWord_1492685) baseStart_1492685 baseEnd_1492685 := by
    simpa [prefixWord, tailWord_1492685, baseEnd_1492685] using wordTrace_append hprefix tailTrace_1492685
  have hstable : (prefixWord ++ tailWord_1492685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492685).length < 2 ^ (prefixWord ++ tailWord_1492685).sum := by decide
  have hdescent : baseEnd_1492685 < baseStart_1492685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492698 : List Nat := [3, 1, 1, 2, 2, 3, 1, 4, 2, 1, 3]
def baseStart_1492698 : Nat := 118140960795 + 1492698 * 2 ^ 59
def prefixEnd_1492698 : Nat := 4983230072969 + 3 ^ 40 * 1492698 * 2
def baseEnd_1492698 : Nat := 766471546005106045910213

theorem tailTrace_1492698 : CollatzResearch.WordTrace tailWord_1492698 prefixEnd_1492698 766471546005106045910213 := by
  unfold tailWord_1492698
  simp only [CollatzResearch.WordTrace]
  refine ⟨13610792186554388341823687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36295445830811702244863165 13610792186554388341823687)
  ·
    refine ⟨20416188279831582512735531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13610792186554388341823687 20416188279831582512735531)
    ·
      refine ⟨30624282419747373769103297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20416188279831582512735531 30624282419747373769103297)
      ·
        refine ⟨22968211814810530326827473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30624282419747373769103297 22968211814810530326827473)
        ·
          refine ⟨17226158861107897745120605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22968211814810530326827473 17226158861107897745120605)
          ·
            refine ⟨6459809572915461654420227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17226158861107897745120605 6459809572915461654420227)
            ·
              refine ⟨9689714359373192481630341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6459809572915461654420227 9689714359373192481630341)
              ·
                refine ⟨1816821442382473590305689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9689714359373192481630341 1816821442382473590305689)
                ·
                  refine ⟨1362616081786855192729267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1816821442382473590305689 1362616081786855192729267)
                  ·
                    refine ⟨2043924122680282789093901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1362616081786855192729267 2043924122680282789093901)
                    ·
                      refine ⟨766471546005106045910213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2043924122680282789093901 766471546005106045910213)
                      ·
                        rfl

theorem cell23_1492698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 4, 2, 1, 3].length) (baseStart_1492698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1492698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1492698 prefixEnd_1492698 := by exact prefixLift 1492698
  have htrace : WordTrace (prefixWord ++ tailWord_1492698) baseStart_1492698 baseEnd_1492698 := by
    simpa [prefixWord, tailWord_1492698, baseEnd_1492698] using wordTrace_append hprefix tailTrace_1492698
  have hstable : (prefixWord ++ tailWord_1492698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492698).length < 2 ^ (prefixWord ++ tailWord_1492698).sum := by decide
  have hdescent : baseEnd_1492698 < baseStart_1492698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492704 : List Nat := [2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 4]
def baseStart_1492704 : Nat := 118140960795 + 1492704 * 2 ^ 59
def prefixEnd_1492704 : Nat := 4983230072969 + 3 ^ 40 * 1492704 * 2
def baseEnd_1492704 : Nat := 766474626889033022435185

theorem tailTrace_1492704 : CollatzResearch.WordTrace tailWord_1492704 prefixEnd_1492704 766474626889033022435185 := by
  unfold tailWord_1492704
  simp only [CollatzResearch.WordTrace]
  refine ⟨27221693792097908196006583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36295591722797210928008777 27221693792097908196006583)
  ·
    refine ⟨40832540688146862294009875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27221693792097908196006583 40832540688146862294009875)
    ·
      refine ⟨61248811032220293441014813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40832540688146862294009875 61248811032220293441014813)
      ·
        refine ⟨22968304137082610040380555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61248811032220293441014813 22968304137082610040380555)
        ·
          refine ⟨34452456205623915060570833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22968304137082610040380555 34452456205623915060570833)
          ·
            refine ⟨25839342154217936295428125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34452456205623915060570833 25839342154217936295428125)
            ·
              refine ⟨9689753307831726110785547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25839342154217936295428125 9689753307831726110785547)
              ·
                refine ⟨14534629961747589166178321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9689753307831726110785547 14534629961747589166178321)
                ·
                  refine ⟨10900972471310691874633741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14534629961747589166178321 10900972471310691874633741)
                  ·
                    refine ⟨4087864676741509452987653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10900972471310691874633741 4087864676741509452987653)
                    ·
                      refine ⟨766474626889033022435185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4087864676741509452987653 766474626889033022435185)
                      ·
                        rfl

theorem cell23_1492704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 4].length) (baseStart_1492704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1492704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1492704 prefixEnd_1492704 := by exact prefixLift 1492704
  have htrace : WordTrace (prefixWord ++ tailWord_1492704) baseStart_1492704 baseEnd_1492704 := by
    simpa [prefixWord, tailWord_1492704, baseEnd_1492704] using wordTrace_append hprefix tailTrace_1492704
  have hstable : (prefixWord ++ tailWord_1492704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492704).length < 2 ^ (prefixWord ++ tailWord_1492704).sum := by decide
  have hdescent : baseEnd_1492704 < baseStart_1492704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492714 : List Nat := [3, 1, 3, 1, 1, 1, 3, 1, 1, 8]
def baseStart_1492714 : Nat := 118140960795 + 1492714 * 2 ^ 59
def prefixEnd_1492714 : Nat := 4983230072969 + 3 ^ 40 * 1492714 * 2
def baseEnd_1492714 : Nat := 255493253898525994436713

theorem tailTrace_1492714 : CollatzResearch.WordTrace tailWord_1492714 prefixEnd_1492714 255493253898525994436713 := by
  unfold tailWord_1492714
  simp only [CollatzResearch.WordTrace]
  refine ⟨13610938078539897024969299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36295834876106392066584797 13610938078539897024969299)
  ·
    refine ⟨20416407117809845537453949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13610938078539897024969299 20416407117809845537453949)
    ·
      refine ⟨7656152669178692076545231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20416407117809845537453949 7656152669178692076545231)
      ·
        refine ⟨11484229003768038114817847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7656152669178692076545231 11484229003768038114817847)
        ·
          refine ⟨17226343505652057172226771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11484229003768038114817847 17226343505652057172226771)
          ·
            refine ⟨25839515258478085758340157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17226343505652057172226771 25839515258478085758340157)
            ·
              refine ⟨9689818221929282159377559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25839515258478085758340157 9689818221929282159377559)
              ·
                refine ⟨14534727332893923239066339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9689818221929282159377559 14534727332893923239066339)
                ·
                  refine ⟨21802090999340884858599509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14534727332893923239066339 21802090999340884858599509)
                  ·
                    refine ⟨255493253898525994436713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 21802090999340884858599509 255493253898525994436713)
                    ·
                      rfl

theorem cell23_1492714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_1492714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1492714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1492714 prefixEnd_1492714 := by exact prefixLift 1492714
  have htrace : WordTrace (prefixWord ++ tailWord_1492714) baseStart_1492714 baseEnd_1492714 := by
    simpa [prefixWord, tailWord_1492714, baseEnd_1492714] using wordTrace_append hprefix tailTrace_1492714
  have hstable : (prefixWord ++ tailWord_1492714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492714).length < 2 ^ (prefixWord ++ tailWord_1492714).sum := by decide
  have hdescent : baseEnd_1492714 < baseStart_1492714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492744 : List Nat := [2, 1, 3, 2, 2, 1, 1, 2, 9]
def baseStart_1492744 : Nat := 118140960795 + 1492744 * 2 ^ 59
def prefixEnd_1492744 : Nat := 4983230072969 + 3 ^ 40 * 1492744 * 2
def baseEnd_1492744 : Nat := 85166129568356985103889

theorem tailTrace_1492744 : CollatzResearch.WordTrace tailWord_1492744 prefixEnd_1492744 85166129568356985103889 := by
  unfold tailWord_1492744
  simp only [CollatzResearch.WordTrace]
  refine ⟨27222423252025451611734643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36296564336033935482312857 27222423252025451611734643)
  ·
    refine ⟨40833634878038177417601965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27222423252025451611734643 40833634878038177417601965)
    ·
      refine ⟨15312613079264316531600737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40833634878038177417601965 15312613079264316531600737)
      ·
        refine ⟨11484459809448237398700553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15312613079264316531600737 11484459809448237398700553)
        ·
          refine ⟨8613344857086178049025415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11484459809448237398700553 8613344857086178049025415)
          ·
            refine ⟨12920017285629267073538123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8613344857086178049025415 12920017285629267073538123)
            ·
              refine ⟨19380025928443900610307185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12920017285629267073538123 19380025928443900610307185)
              ·
                refine ⟨14535019446332925457730389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19380025928443900610307185 14535019446332925457730389)
                ·
                  refine ⟨85166129568356985103889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 14535019446332925457730389 85166129568356985103889)
                  ·
                    rfl

theorem cell23_1492744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 9].length) (baseStart_1492744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1492744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1492744 prefixEnd_1492744 := by exact prefixLift 1492744
  have htrace : WordTrace (prefixWord ++ tailWord_1492744) baseStart_1492744 baseEnd_1492744 := by
    simpa [prefixWord, tailWord_1492744, baseEnd_1492744] using wordTrace_append hprefix tailTrace_1492744
  have hstable : (prefixWord ++ tailWord_1492744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492744).length < 2 ^ (prefixWord ++ tailWord_1492744).sum := by decide
  have hdescent : baseEnd_1492744 < baseStart_1492744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492766 : List Nat := [4, 3, 2, 2, 1, 1, 3, 1, 2, 1, 3]
def baseStart_1492766 : Nat := 118140960795 + 1492766 * 2 ^ 59
def prefixEnd_1492766 : Nat := 4983230072969 + 3 ^ 40 * 1492766 * 2
def baseEnd_1492766 : Nat := 766506462689611779859901

theorem tailTrace_1492766 : CollatzResearch.WordTrace tailWord_1492766 prefixEnd_1492766 766506462689611779859901 := by
  unfold tailWord_1492766
  simp only [CollatzResearch.WordTrace]
  refine ⟨6805706113746400122596269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36297099273314133987180101 6805706113746400122596269)
  ·
    refine ⟨2552139792654900045973601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6805706113746400122596269 2552139792654900045973601)
    ·
      refine ⟨1914104844491175034480201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2552139792654900045973601 1914104844491175034480201)
      ·
        refine ⟨1435578633368381275860151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1914104844491175034480201 1435578633368381275860151)
        ·
          refine ⟨2153367950052571913790227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1435578633368381275860151 2153367950052571913790227)
          ·
            refine ⟨3230051925078857870685341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2153367950052571913790227 3230051925078857870685341)
            ·
              refine ⟨1211269471904571701507003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3230051925078857870685341 1211269471904571701507003)
              ·
                refine ⟨1816904207856857552260505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1211269471904571701507003 1816904207856857552260505)
                ·
                  refine ⟨1362678155892643164195379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1816904207856857552260505 1362678155892643164195379)
                  ·
                    refine ⟨2044017233838964746293069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1362678155892643164195379 2044017233838964746293069)
                    ·
                      refine ⟨766506462689611779859901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2044017233838964746293069 766506462689611779859901)
                      ·
                        rfl

theorem cell23_1492766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_1492766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1492766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1492766 prefixEnd_1492766 := by exact prefixLift 1492766
  have htrace : WordTrace (prefixWord ++ tailWord_1492766) baseStart_1492766 baseEnd_1492766 := by
    simpa [prefixWord, tailWord_1492766, baseEnd_1492766] using wordTrace_append hprefix tailTrace_1492766
  have hstable : (prefixWord ++ tailWord_1492766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492766).length < 2 ^ (prefixWord ++ tailWord_1492766).sum := by decide
  have hdescent : baseEnd_1492766 < baseStart_1492766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492771 : List Nat := [1, 1, 1, 4, 2, 1, 4, 1, 2, 3, 3]
def baseStart_1492771 : Nat := 118140960795 + 1492771 * 2 ^ 59
def prefixEnd_1492771 : Nat := 4983230072969 + 3 ^ 40 * 1492771 * 2
def baseEnd_1492771 : Nat := 766509030092884260297377

theorem tailTrace_1492771 : CollatzResearch.WordTrace tailWord_1492771 prefixEnd_1492771 766509030092884260297377 := by
  unfold tailWord_1492771
  simp only [CollatzResearch.WordTrace]
  refine ⟨54445831274953086834702167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36297220849968724556468111 54445831274953086834702167)
  ·
    refine ⟨81668746912429630252053251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54445831274953086834702167 81668746912429630252053251)
    ·
      refine ⟨122503120368644445378079877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81668746912429630252053251 122503120368644445378079877)
      ·
        refine ⟨22969335069120833508389977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122503120368644445378079877 22969335069120833508389977)
        ·
          refine ⟨17227001301840625131292483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22969335069120833508389977 17227001301840625131292483)
          ·
            refine ⟨25840501952760937696938725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17227001301840625131292483 25840501952760937696938725)
            ·
              refine ⟨4845094116142675818176011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25840501952760937696938725 4845094116142675818176011)
              ·
                refine ⟨7267641174214013727264017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4845094116142675818176011 7267641174214013727264017)
                ·
                  refine ⟨5450730880660510295448013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7267641174214013727264017 5450730880660510295448013)
                  ·
                    refine ⟨2044024080247691360793005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5450730880660510295448013 2044024080247691360793005)
                    ·
                      refine ⟨766509030092884260297377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2044024080247691360793005 766509030092884260297377)
                      ·
                        rfl

theorem cell23_1492771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 2, 3, 3].length) (baseStart_1492771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1492771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1492771 prefixEnd_1492771 := by exact prefixLift 1492771
  have htrace : WordTrace (prefixWord ++ tailWord_1492771) baseStart_1492771 baseEnd_1492771 := by
    simpa [prefixWord, tailWord_1492771, baseEnd_1492771] using wordTrace_append hprefix tailTrace_1492771
  have hstable : (prefixWord ++ tailWord_1492771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492771).length < 2 ^ (prefixWord ++ tailWord_1492771).sum := by decide
  have hdescent : baseEnd_1492771 < baseStart_1492771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492784 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 5]
def baseStart_1492784 : Nat := 118140960795 + 1492784 * 2 ^ 59
def prefixEnd_1492784 : Nat := 4983230072969 + 3 ^ 40 * 1492784 * 2
def baseEnd_1492784 : Nat := 766515705341392709434817

theorem tailTrace_1492784 : CollatzResearch.WordTrace tailWord_1492784 prefixEnd_1492784 766515705341392709434817 := by
  unfold tailWord_1492784
  simp only [CollatzResearch.WordTrace]
  refine ⟨27223152711952995027462703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36297536949270660036616937 27223152711952995027462703)
  ·
    refine ⟨40834729067929492541194055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27223152711952995027462703 40834729067929492541194055)
    ·
      refine ⟨61252093601894238811791083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40834729067929492541194055 61252093601894238811791083)
      ·
        refine ⟨91878140402841358217686625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61252093601894238811791083 91878140402841358217686625)
        ·
          refine ⟨68908605302131018663264969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91878140402841358217686625 68908605302131018663264969)
          ·
            refine ⟨51681453976598263997448727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68908605302131018663264969 51681453976598263997448727)
            ·
              refine ⟨77522180964897395996173091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51681453976598263997448727 77522180964897395996173091)
              ·
                refine ⟨116283271447346093994259637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77522180964897395996173091 116283271447346093994259637)
                ·
                  refine ⟨10901556698188696311961841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 116283271447346093994259637 10901556698188696311961841)
                  ·
                    refine ⟨8176167523641522233971381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10901556698188696311961841 8176167523641522233971381)
                    ·
                      refine ⟨766515705341392709434817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8176167523641522233971381 766515705341392709434817)
                      ·
                        rfl

theorem cell23_1492784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 5].length) (baseStart_1492784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1492784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1492784 prefixEnd_1492784 := by exact prefixLift 1492784
  have htrace : WordTrace (prefixWord ++ tailWord_1492784) baseStart_1492784 baseEnd_1492784 := by
    simpa [prefixWord, tailWord_1492784, baseEnd_1492784] using wordTrace_append hprefix tailTrace_1492784
  have hstable : (prefixWord ++ tailWord_1492784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492784).length < 2 ^ (prefixWord ++ tailWord_1492784).sum := by decide
  have hdescent : baseEnd_1492784 < baseStart_1492784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492872 : List Nat := [2, 1, 3, 3, 3, 1, 1, 4, 1, 4]
def baseStart_1492872 : Nat := 118140960795 + 1492872 * 2 ^ 59
def prefixEnd_1492872 : Nat := 4983230072969 + 3 ^ 40 * 1492872 * 2
def baseEnd_1492872 : Nat := 255520297212996121711471

theorem tailTrace_1492872 : CollatzResearch.WordTrace tailWord_1492872 prefixEnd_1492872 255520297212996121711471 := by
  unfold tailWord_1492872
  simp only [CollatzResearch.WordTrace]
  refine ⟨27224757523793590542064435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36299676698391454056085913 27224757523793590542064435)
  ·
    refine ⟨40837136285690385813096653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27224757523793590542064435 40837136285690385813096653)
    ·
      refine ⟨15313926107133894679911245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40837136285690385813096653 15313926107133894679911245)
      ·
        refine ⟨5742722290175210504966717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15313926107133894679911245 5742722290175210504966717)
        ·
          refine ⟨2153520858815703939362519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5742722290175210504966717 2153520858815703939362519)
          ·
            refine ⟨3230281288223555909043779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2153520858815703939362519 3230281288223555909043779)
            ·
              refine ⟨4845421932335333863565669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3230281288223555909043779 4845421932335333863565669)
              ·
                refine ⟨908516612312875099418563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4845421932335333863565669 908516612312875099418563)
                ·
                  refine ⟨1362774918469312649127845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 908516612312875099418563 1362774918469312649127845)
                  ·
                    refine ⟨255520297212996121711471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1362774918469312649127845 255520297212996121711471)
                    ·
                      rfl

theorem cell23_1492872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 4, 1, 4].length) (baseStart_1492872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1492872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1492872 prefixEnd_1492872 := by exact prefixLift 1492872
  have htrace : WordTrace (prefixWord ++ tailWord_1492872) baseStart_1492872 baseEnd_1492872 := by
    simpa [prefixWord, tailWord_1492872, baseEnd_1492872] using wordTrace_append hprefix tailTrace_1492872
  have hstable : (prefixWord ++ tailWord_1492872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492872).length < 2 ^ (prefixWord ++ tailWord_1492872).sum := by decide
  have hdescent : baseEnd_1492872 < baseStart_1492872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492881 : List Nat := [1, 2, 2, 1, 1, 1, 5, 2, 3, 5]
def baseStart_1492881 : Nat := 118140960795 + 1492881 * 2 ^ 59
def prefixEnd_1492881 : Nat := 4983230072969 + 3 ^ 40 * 1492881 * 2
def baseEnd_1492881 : Nat := 255521837654959609973957

theorem tailTrace_1492881 : CollatzResearch.WordTrace tailWord_1492881 prefixEnd_1492881 255521837654959609973957 := by
  unfold tailWord_1492881
  simp only [CollatzResearch.WordTrace]
  refine ⟨54449843304554575621206497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36299895536369717080804331 54449843304554575621206497)
  ·
    refine ⟨40837382478415931715904873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54449843304554575621206497 40837382478415931715904873)
    ·
      refine ⟨30628036858811948786928655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40837382478415931715904873 30628036858811948786928655)
      ·
        refine ⟨45942055288217923180392983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30628036858811948786928655 45942055288217923180392983)
        ·
          refine ⟨68913082932326884770589475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45942055288217923180392983 68913082932326884770589475)
          ·
            refine ⟨103369624398490327155884213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68913082932326884770589475 103369624398490327155884213)
            ·
              refine ⟨9690902287358468170864145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 103369624398490327155884213 9690902287358468170864145)
              ·
                refine ⟨7268176715518851128148109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9690902287358468170864145 7268176715518851128148109)
                ·
                  refine ⟨2725566268319569173055541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7268176715518851128148109 2725566268319569173055541)
                  ·
                    refine ⟨255521837654959609973957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2725566268319569173055541 255521837654959609973957)
                    ·
                      rfl

theorem cell23_1492881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 5].length) (baseStart_1492881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1492881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1492881 prefixEnd_1492881 := by exact prefixLift 1492881
  have htrace : WordTrace (prefixWord ++ tailWord_1492881) baseStart_1492881 baseEnd_1492881 := by
    simpa [prefixWord, tailWord_1492881, baseEnd_1492881] using wordTrace_append hprefix tailTrace_1492881
  have hstable : (prefixWord ++ tailWord_1492881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492881).length < 2 ^ (prefixWord ++ tailWord_1492881).sum := by decide
  have hdescent : baseEnd_1492881 < baseStart_1492881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492911 : List Nat := [1, 1, 2, 1, 2, 2, 3, 4, 1, 6]
def baseStart_1492911 : Nat := 118140960795 + 1492911 * 2 ^ 59
def prefixEnd_1492911 : Nat := 4983230072969 + 3 ^ 40 * 1492911 * 2
def baseEnd_1492911 : Nat := 255526972461504570848911

theorem tailTrace_1492911 : CollatzResearch.WordTrace tailWord_1492911 prefixEnd_1492911 255526972461504570848911 := by
  unfold tailWord_1492911
  simp only [CollatzResearch.WordTrace]
  refine ⟨54450937494445890744798587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36300624996297260496532391 54450937494445890744798587)
  ·
    refine ⟨81676406241668836117197881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54450937494445890744798587 81676406241668836117197881)
    ·
      refine ⟨61257304681251627087898411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81676406241668836117197881 61257304681251627087898411)
      ·
        refine ⟨91885957021877440631847617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61257304681251627087898411 91885957021877440631847617)
        ·
          refine ⟨68914467766408080473885713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91885957021877440631847617 68914467766408080473885713)
          ·
            refine ⟨51685850824806060355414285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68914467766408080473885713 51685850824806060355414285)
            ·
              refine ⟨19382194059302272633280357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51685850824806060355414285 19382194059302272633280357)
              ·
                refine ⟨3634161386119176118740067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19382194059302272633280357 3634161386119176118740067)
                ·
                  refine ⟨5451242079178764178110101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3634161386119176118740067 5451242079178764178110101)
                  ·
                    refine ⟨255526972461504570848911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5451242079178764178110101 255526972461504570848911)
                    ·
                      rfl

theorem cell23_1492911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 4, 1, 6].length) (baseStart_1492911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1492911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1492911 prefixEnd_1492911 := by exact prefixLift 1492911
  have htrace : WordTrace (prefixWord ++ tailWord_1492911) baseStart_1492911 baseEnd_1492911 := by
    simpa [prefixWord, tailWord_1492911, baseEnd_1492911] using wordTrace_append hprefix tailTrace_1492911
  have hstable : (prefixWord ++ tailWord_1492911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492911).length < 2 ^ (prefixWord ++ tailWord_1492911).sum := by decide
  have hdescent : baseEnd_1492911 < baseStart_1492911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492928 : List Nat := [2, 1, 1, 2, 3, 2, 3, 1, 4, 4]
def baseStart_1492928 : Nat := 118140960795 + 1492928 * 2 ^ 59
def prefixEnd_1492928 : Nat := 4983230072969 + 3 ^ 40 * 1492928 * 2
def baseEnd_1492928 : Nat := 255529882185213382011385

theorem tailTrace_1492928 : CollatzResearch.WordTrace tailWord_1492928 prefixEnd_1492928 255529882185213382011385 := by
  unfold tailWord_1492928
  simp only [CollatzResearch.WordTrace]
  refine ⟨27225778767692151324083719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36301038356922868432111625 27225778767692151324083719)
  ·
    refine ⟨40838668151538226986125579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27225778767692151324083719 40838668151538226986125579)
    ·
      refine ⟨61258002227307340479188369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40838668151538226986125579 61258002227307340479188369)
      ·
        refine ⟨45943501670480505359391277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61258002227307340479188369 45943501670480505359391277)
        ·
          refine ⟨17228813126430189509771729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45943501670480505359391277 17228813126430189509771729)
          ·
            refine ⟨12921609844822642132328797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17228813126430189509771729 12921609844822642132328797)
            ·
              refine ⟨4845603691808490799623299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12921609844822642132328797 4845603691808490799623299)
              ·
                refine ⟨7268405537712736199434949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4845603691808490799623299 7268405537712736199434949)
                ·
                  refine ⟨1362826038321138037394053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7268405537712736199434949 1362826038321138037394053)
                  ·
                    refine ⟨255529882185213382011385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1362826038321138037394053 255529882185213382011385)
                    ·
                      rfl

theorem cell23_1492928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 4, 4].length) (baseStart_1492928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1492928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1492928 prefixEnd_1492928 := by exact prefixLift 1492928
  have htrace : WordTrace (prefixWord ++ tailWord_1492928) baseStart_1492928 baseEnd_1492928 := by
    simpa [prefixWord, tailWord_1492928, baseEnd_1492928] using wordTrace_append hprefix tailTrace_1492928
  have hstable : (prefixWord ++ tailWord_1492928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492928).length < 2 ^ (prefixWord ++ tailWord_1492928).sum := by decide
  have hdescent : baseEnd_1492928 < baseStart_1492928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492938 : List Nat := [3, 1, 2, 1, 2, 1, 2, 1, 5, 2, 3]
def baseStart_1492938 : Nat := 118140960795 + 1492938 * 2 ^ 59
def prefixEnd_1492938 : Nat := 4983230072969 + 3 ^ 40 * 1492938 * 2
def baseEnd_1492938 : Nat := 766594781362185106909109

theorem tailTrace_1492938 : CollatzResearch.WordTrace tailWord_1492938 prefixEnd_1492938 766594781362185106909109 := by
  unfold tailWord_1492938
  simp only [CollatzResearch.WordTrace]
  refine ⟨13612980566337018589007867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36301281510232049570687645 13612980566337018589007867)
  ·
    refine ⟨20419470849505527883511801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13612980566337018589007867 20419470849505527883511801)
    ·
      refine ⟨15314603137129145912633851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20419470849505527883511801 15314603137129145912633851)
      ·
        refine ⟨22971904705693718868950777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15314603137129145912633851 22971904705693718868950777)
        ·
          refine ⟨17228928529270289151713083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22971904705693718868950777 17228928529270289151713083)
          ·
            refine ⟨25843392793905433727569625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17228928529270289151713083 25843392793905433727569625)
            ·
              refine ⟨19382544595429075295677219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25843392793905433727569625 19382544595429075295677219)
              ·
                refine ⟨29073816893143612943515829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19382544595429075295677219 29073816893143612943515829)
                ·
                  refine ⟨2725670333732213713454609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29073816893143612943515829 2725670333732213713454609)
                  ·
                    refine ⟨2044252750299160285090957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2725670333732213713454609 2044252750299160285090957)
                    ·
                      refine ⟨766594781362185106909109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2044252750299160285090957 766594781362185106909109)
                      ·
                        rfl

theorem cell23_1492938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 5, 2, 3].length) (baseStart_1492938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1492938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1492938 prefixEnd_1492938 := by exact prefixLift 1492938
  have htrace : WordTrace (prefixWord ++ tailWord_1492938) baseStart_1492938 baseEnd_1492938 := by
    simpa [prefixWord, tailWord_1492938, baseEnd_1492938] using wordTrace_append hprefix tailTrace_1492938
  have hstable : (prefixWord ++ tailWord_1492938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492938).length < 2 ^ (prefixWord ++ tailWord_1492938).sum := by decide
  have hdescent : baseEnd_1492938 < baseStart_1492938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492948 : List Nat := [2, 4, 1, 2, 1, 1, 3, 1, 1, 1, 6]
def baseStart_1492948 : Nat := 118140960795 + 1492948 * 2 ^ 59
def prefixEnd_1492948 : Nat := 4983230072969 + 3 ^ 40 * 1492948 * 2
def baseEnd_1492948 : Nat := 766599916168730067784063

theorem tailTrace_1492948 : CollatzResearch.WordTrace tailWord_1492948 prefixEnd_1492948 766599916168730067784063 := by
  unfold tailWord_1492948
  simp only [CollatzResearch.WordTrace]
  refine ⟨27226143497655923031947749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36301524663541230709263665 27226143497655923031947749)
  ·
    refine ⟨5104901905810485568490203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27226143497655923031947749 5104901905810485568490203)
    ·
      refine ⟨7657352858715728352735305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5104901905810485568490203 7657352858715728352735305)
      ·
        refine ⟨5743014644036796264551479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7657352858715728352735305 5743014644036796264551479)
        ·
          refine ⟨8614521966055194396827219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5743014644036796264551479 8614521966055194396827219)
          ·
            refine ⟨12921782949082791595240829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8614521966055194396827219 12921782949082791595240829)
            ·
              refine ⟨4845668605906046848215311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12921782949082791595240829 4845668605906046848215311)
              ·
                refine ⟨7268502908859070272322967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4845668605906046848215311 7268502908859070272322967)
                ·
                  refine ⟨10902754363288605408484451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7268502908859070272322967 10902754363288605408484451)
                  ·
                    refine ⟨16354131544932908112726677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10902754363288605408484451 16354131544932908112726677)
                    ·
                      refine ⟨766599916168730067784063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16354131544932908112726677 766599916168730067784063)
                      ·
                        rfl

theorem cell23_1492948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_1492948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1492948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1492948 prefixEnd_1492948 := by exact prefixLift 1492948
  have htrace : WordTrace (prefixWord ++ tailWord_1492948) baseStart_1492948 baseEnd_1492948 := by
    simpa [prefixWord, tailWord_1492948, baseEnd_1492948] using wordTrace_append hprefix tailTrace_1492948
  have hstable : (prefixWord ++ tailWord_1492948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492948).length < 2 ^ (prefixWord ++ tailWord_1492948).sum := by decide
  have hdescent : baseEnd_1492948 < baseStart_1492948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492968 : List Nat := [2, 1, 4, 1, 1, 1, 1, 3, 3, 3, 3]
def baseStart_1492968 : Nat := 118140960795 + 1492968 * 2 ^ 59
def prefixEnd_1492968 : Nat := 4983230072969 + 3 ^ 40 * 1492968 * 2
def baseEnd_1492968 : Nat := 766610185781819989533971

theorem tailTrace_1492968 : CollatzResearch.WordTrace tailWord_1492968 prefixEnd_1492968 766610185781819989533971 := by
  unfold tailWord_1492968
  simp only [CollatzResearch.WordTrace]
  refine ⟨27226508227619694739811779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36302010970159592986415705 27226508227619694739811779)
  ·
    refine ⟨40839762341429542109717669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27226508227619694739811779 40839762341429542109717669)
    ·
      refine ⟨7657455439018039145572063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40839762341429542109717669 7657455439018039145572063)
      ·
        refine ⟨11486183158527058718358095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7657455439018039145572063 11486183158527058718358095)
        ·
          refine ⟨17229274737790588077537143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11486183158527058718358095 17229274737790588077537143)
          ·
            refine ⟨25843912106685882116305715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17229274737790588077537143 25843912106685882116305715)
            ·
              refine ⟨38765868160028823174458573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25843912106685882116305715 38765868160028823174458573)
              ·
                refine ⟨14537200560010808690421965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38765868160028823174458573 14537200560010808690421965)
                ·
                  refine ⟨5451450210004053258908237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14537200560010808690421965 5451450210004053258908237)
                  ·
                    refine ⟨2044293828751519972090589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5451450210004053258908237 2044293828751519972090589)
                    ·
                      refine ⟨766610185781819989533971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2044293828751519972090589 766610185781819989533971)
                      ·
                        rfl

theorem cell23_1492968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 3, 3, 3].length) (baseStart_1492968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1492968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1492968 prefixEnd_1492968 := by exact prefixLift 1492968
  have htrace : WordTrace (prefixWord ++ tailWord_1492968) baseStart_1492968 baseEnd_1492968 := by
    simpa [prefixWord, tailWord_1492968, baseEnd_1492968] using wordTrace_append hprefix tailTrace_1492968
  have hstable : (prefixWord ++ tailWord_1492968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492968).length < 2 ^ (prefixWord ++ tailWord_1492968).sum := by decide
  have hdescent : baseEnd_1492968 < baseStart_1492968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492985 : List Nat := [1, 2, 1, 3, 1, 4, 2, 1, 4, 1, 3]
def baseStart_1492985 : Nat := 118140960795 + 1492985 * 2 ^ 59
def prefixEnd_1492985 : Nat := 4983230072969 + 3 ^ 40 * 1492985 * 2
def baseEnd_1492985 : Nat := 766618914952946423021393

theorem tailTrace_1492985 : CollatzResearch.WordTrace tailWord_1492985 prefixEnd_1492985 766618914952946423021393 := by
  unfold tailWord_1492985
  simp only [CollatzResearch.WordTrace]
  refine ⟨54453636496177801382992409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36302424330785200921994939 54453636496177801382992409)
  ·
    refine ⟨40840227372133351037244307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54453636496177801382992409 40840227372133351037244307)
    ·
      refine ⟨61260341058200026555866461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40840227372133351037244307 61260341058200026555866461)
      ·
        refine ⟨22972627896825009958449923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61260341058200026555866461 22972627896825009958449923)
        ·
          refine ⟨34458941845237514937674885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22972627896825009958449923 34458941845237514937674885)
          ·
            refine ⟨6461051595982034050814041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34458941845237514937674885 6461051595982034050814041)
            ·
              refine ⟨4845788696986525538110531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6461051595982034050814041 4845788696986525538110531)
              ·
                refine ⟨7268683045479788307165797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4845788696986525538110531 7268683045479788307165797)
                ·
                  refine ⟨1362878071027460307593587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7268683045479788307165797 1362878071027460307593587)
                  ·
                    refine ⟨2044317106541190461390381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1362878071027460307593587 2044317106541190461390381)
                    ·
                      refine ⟨766618914952946423021393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2044317106541190461390381 766618914952946423021393)
                      ·
                        rfl

theorem cell23_1492985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 4, 1, 3].length) (baseStart_1492985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1492985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1492985 prefixEnd_1492985 := by exact prefixLift 1492985
  have htrace : WordTrace (prefixWord ++ tailWord_1492985) baseStart_1492985 baseEnd_1492985 := by
    simpa [prefixWord, tailWord_1492985, baseEnd_1492985] using wordTrace_append hprefix tailTrace_1492985
  have hstable : (prefixWord ++ tailWord_1492985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492985).length < 2 ^ (prefixWord ++ tailWord_1492985).sum := by decide
  have hdescent : baseEnd_1492985 < baseStart_1492985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1492996 : List Nat := [2, 3, 2, 4, 1, 2, 2, 1, 2, 4]
def baseStart_1492996 : Nat := 118140960795 + 1492996 * 2 ^ 59
def prefixEnd_1492996 : Nat := 4983230072969 + 3 ^ 40 * 1492996 * 2
def baseEnd_1492996 : Nat := 255541521080048626661281

theorem tailTrace_1492996 : CollatzResearch.WordTrace tailWord_1492996 prefixEnd_1492996 255541521080048626661281 := by
  unfold tailWord_1492996
  simp only [CollatzResearch.WordTrace]
  refine ⟨27227018849568975130821421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36302691799425300174428561 27227018849568975130821421)
  ·
    refine ⟨10210132068588365674058033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27227018849568975130821421 10210132068588365674058033)
    ·
      refine ⟨7657599051441274255543525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10210132068588365674058033 7657599051441274255543525)
      ·
        refine ⟨1435799822145238922914411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7657599051441274255543525 1435799822145238922914411)
        ·
          refine ⟨2153699733217858384371617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1435799822145238922914411 2153699733217858384371617)
          ·
            refine ⟨1615274799913393788278713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2153699733217858384371617 1615274799913393788278713)
            ·
              refine ⟨1211456099935045341209035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1615274799913393788278713 1211456099935045341209035)
              ·
                refine ⟨1817184149902568011813553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1211456099935045341209035 1817184149902568011813553)
                ·
                  refine ⟨1362888112426926008860165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1817184149902568011813553 1362888112426926008860165)
                  ·
                    refine ⟨255541521080048626661281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1362888112426926008860165 255541521080048626661281)
                    ·
                      rfl

theorem cell23_1492996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 2, 1, 2, 4].length) (baseStart_1492996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1492996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1492996 prefixEnd_1492996 := by exact prefixLift 1492996
  have htrace : WordTrace (prefixWord ++ tailWord_1492996) baseStart_1492996 baseEnd_1492996 := by
    simpa [prefixWord, tailWord_1492996, baseEnd_1492996] using wordTrace_append hprefix tailTrace_1492996
  have hstable : (prefixWord ++ tailWord_1492996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1492996).length < 2 ^ (prefixWord ++ tailWord_1492996).sum := by decide
  have hdescent : baseEnd_1492996 < baseStart_1492996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1492996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493029 : List Nat := [1, 3, 1, 2, 2, 4, 3, 1, 1, 3, 2]
def baseStart_1493029 : Nat := 118140960795 + 1493029 * 2 ^ 59
def prefixEnd_1493029 : Nat := 4983230072969 + 3 ^ 40 * 1493029 * 2
def baseEnd_1493029 : Nat := 766641508101744250871191

theorem tailTrace_1493029 : CollatzResearch.WordTrace tailWord_1493029 prefixEnd_1493029 766641508101744250871191 := by
  unfold tailWord_1493029
  simp only [CollatzResearch.WordTrace]
  refine ⟨54455241308018396897594141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36303494205345597931729427 54455241308018396897594141)
  ·
    refine ⟨20420715490506898836597803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54455241308018396897594141 20420715490506898836597803)
    ·
      refine ⟨30631073235760348254896705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20420715490506898836597803 30631073235760348254896705)
      ·
        refine ⟨22973304926820261191172529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30631073235760348254896705 22973304926820261191172529)
        ·
          refine ⟨17229978695115195893379397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22973304926820261191172529 17229978695115195893379397)
          ·
            refine ⟨3230621005334099230008637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17229978695115195893379397 3230621005334099230008637)
            ·
              refine ⟨1211482877000287211253239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3230621005334099230008637 1211482877000287211253239)
              ·
                refine ⟨1817224315500430816879859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1211482877000287211253239 1817224315500430816879859)
                ·
                  refine ⟨2725836473250646225319789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1817224315500430816879859 2725836473250646225319789)
                  ·
                    refine ⟨1022188677468992334494921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2725836473250646225319789 1022188677468992334494921)
                    ·
                      refine ⟨766641508101744250871191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1022188677468992334494921 766641508101744250871191)
                      ·
                        rfl

theorem cell23_1493029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 3, 1, 1, 3, 2].length) (baseStart_1493029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1493029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1493029 prefixEnd_1493029 := by exact prefixLift 1493029
  have htrace : WordTrace (prefixWord ++ tailWord_1493029) baseStart_1493029 baseEnd_1493029 := by
    simpa [prefixWord, tailWord_1493029, baseEnd_1493029] using wordTrace_append hprefix tailTrace_1493029
  have hstable : (prefixWord ++ tailWord_1493029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493029).length < 2 ^ (prefixWord ++ tailWord_1493029).sum := by decide
  have hdescent : baseEnd_1493029 < baseStart_1493029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493062 : List Nat := [6, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3]
def baseStart_1493062 : Nat := 118140960795 + 1493062 * 2 ^ 59
def prefixEnd_1493062 : Nat := 4983230072969 + 3 ^ 40 * 1493062 * 2
def baseEnd_1493062 : Nat := 766658452963342621758539

theorem tailTrace_1493062 : CollatzResearch.WordTrace tailWord_1493062 prefixEnd_1493062 766658452963342621758539 := by
  unfold tailWord_1493062
  simp only [CollatzResearch.WordTrace]
  refine ⟨1701763903653088860423295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 36304296611265895689030293 1701763903653088860423295)
  ·
    refine ⟨2552645855479633290634943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1701763903653088860423295 2552645855479633290634943)
    ·
      refine ⟨3828968783219449935952415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2552645855479633290634943 3828968783219449935952415)
      ·
        refine ⟨5743453174829174903928623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3828968783219449935952415 5743453174829174903928623)
        ·
          refine ⟨8615179762243762355892935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5743453174829174903928623 8615179762243762355892935)
          ·
            refine ⟨12922769643365643533839403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8615179762243762355892935 12922769643365643533839403)
            ·
              refine ⟨19384154465048465300759105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12922769643365643533839403 19384154465048465300759105)
              ·
                refine ⟨14538115848786348975569329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19384154465048465300759105 14538115848786348975569329)
                ·
                  refine ⟨10903586886589761731676997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14538115848786348975569329 10903586886589761731676997)
                  ·
                    refine ⟨2044422541235580324689437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10903586886589761731676997 2044422541235580324689437)
                    ·
                      refine ⟨766658452963342621758539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2044422541235580324689437 766658452963342621758539)
                      ·
                        rfl

theorem cell23_1493062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_1493062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1493062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1493062 prefixEnd_1493062 := by exact prefixLift 1493062
  have htrace : WordTrace (prefixWord ++ tailWord_1493062) baseStart_1493062 baseEnd_1493062 := by
    simpa [prefixWord, tailWord_1493062, baseEnd_1493062] using wordTrace_append hprefix tailTrace_1493062
  have hstable : (prefixWord ++ tailWord_1493062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493062).length < 2 ^ (prefixWord ++ tailWord_1493062).sum := by decide
  have hdescent : baseEnd_1493062 < baseStart_1493062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493152 : List Nat := [2, 1, 1, 4, 2, 3, 1, 2, 2, 2, 3]
def baseStart_1493152 : Nat := 118140960795 + 1493152 * 2 ^ 59
def prefixEnd_1493152 : Nat := 4983230072969 + 3 ^ 40 * 1493152 * 2
def baseEnd_1493152 : Nat := 766704666222247269633125

theorem tailTrace_1493152 : CollatzResearch.WordTrace tailWord_1493152 prefixEnd_1493152 766704666222247269633125 := by
  unfold tailWord_1493152
  simp only [CollatzResearch.WordTrace]
  refine ⟨27229863743286394452160855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36306484991048525936214473 27229863743286394452160855)
  ·
    refine ⟨40844795614929591678241283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27229863743286394452160855 40844795614929591678241283)
    ·
      refine ⟨61267193422394387517361925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40844795614929591678241283 61267193422394387517361925)
      ·
        refine ⟨11487598766698947659505361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61267193422394387517361925 11487598766698947659505361)
        ·
          refine ⟨8615699075024210744629021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11487598766698947659505361 8615699075024210744629021)
          ·
            refine ⟨3230887153134079029235883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8615699075024210744629021 3230887153134079029235883)
            ·
              refine ⟨4846330729701118543853825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3230887153134079029235883 4846330729701118543853825)
              ·
                refine ⟨3634748047275838907890369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4846330729701118543853825 3634748047275838907890369)
                ·
                  refine ⟨2726061035456879180917777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3634748047275838907890369 2726061035456879180917777)
                  ·
                    refine ⟨2044545776592659385688333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2726061035456879180917777 2044545776592659385688333)
                    ·
                      refine ⟨766704666222247269633125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2044545776592659385688333 766704666222247269633125)
                      ·
                        rfl

theorem cell23_1493152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 2, 2, 2, 3].length) (baseStart_1493152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1493152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1493152 prefixEnd_1493152 := by exact prefixLift 1493152
  have htrace : WordTrace (prefixWord ++ tailWord_1493152) baseStart_1493152 baseEnd_1493152 := by
    simpa [prefixWord, tailWord_1493152, baseEnd_1493152] using wordTrace_append hprefix tailTrace_1493152
  have hstable : (prefixWord ++ tailWord_1493152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493152).length < 2 ^ (prefixWord ++ tailWord_1493152).sum := by decide
  have hdescent : baseEnd_1493152 < baseStart_1493152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493186 : List Nat := [3, 5, 1, 1, 1, 1, 1, 3, 2, 2, 3]
def baseStart_1493186 : Nat := 118140960795 + 1493186 * 2 ^ 59
def prefixEnd_1493186 : Nat := 4983230072969 + 3 ^ 40 * 1493186 * 2
def baseEnd_1493186 : Nat := 766722124564500136607969

theorem tailTrace_1493186 : CollatzResearch.WordTrace tailWord_1493186 prefixEnd_1493186 766722124564500136607969 := by
  unfold tailWord_1493186
  simp only [CollatzResearch.WordTrace]
  refine ⟨13615241892112403177764853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36307311712299741807372941 13615241892112403177764853)
  ·
    refine ⟨1276428927385537797915455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13615241892112403177764853 1276428927385537797915455)
    ·
      refine ⟨1914643391078306696873183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1276428927385537797915455 1914643391078306696873183)
      ·
        refine ⟨2871965086617460045309775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1914643391078306696873183 2871965086617460045309775)
        ·
          refine ⟨4307947629926190067964663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2871965086617460045309775 4307947629926190067964663)
          ·
            refine ⟨6461921444889285101946995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4307947629926190067964663 6461921444889285101946995)
            ·
              refine ⟨9692882167333927652920493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6461921444889285101946995 9692882167333927652920493)
              ·
                refine ⟨3634830812750222869845185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9692882167333927652920493 3634830812750222869845185)
                ·
                  refine ⟨2726123109562667152383889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3634830812750222869845185 2726123109562667152383889)
                  ·
                    refine ⟨2044592332172000364287917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2726123109562667152383889 2044592332172000364287917)
                    ·
                      refine ⟨766722124564500136607969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2044592332172000364287917 766722124564500136607969)
                      ·
                        rfl

theorem cell23_1493186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_1493186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1493186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1493186 prefixEnd_1493186 := by exact prefixLift 1493186
  have htrace : WordTrace (prefixWord ++ tailWord_1493186) baseStart_1493186 baseEnd_1493186 := by
    simpa [prefixWord, tailWord_1493186, baseEnd_1493186] using wordTrace_append hprefix tailTrace_1493186
  have hstable : (prefixWord ++ tailWord_1493186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493186).length < 2 ^ (prefixWord ++ tailWord_1493186).sum := by decide
  have hdescent : baseEnd_1493186 < baseStart_1493186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493199 : List Nat := [1, 1, 2, 1, 1, 3, 4, 5, 1, 1, 3]
def baseStart_1493199 : Nat := 118140960795 + 1493199 * 2 ^ 59
def prefixEnd_1493199 : Nat := 4983230072969 + 3 ^ 40 * 1493199 * 2
def baseEnd_1493199 : Nat := 766728799813008585745409

theorem tailTrace_1493199 : CollatzResearch.WordTrace tailWord_1493199 prefixEnd_1493199 766728799813008585745409 := by
  unfold tailWord_1493199
  simp only [CollatzResearch.WordTrace]
  refine ⟨54461441717402515931282651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36307627811601677287521767 54461441717402515931282651)
  ·
    refine ⟨81692162576103773896923977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54461441717402515931282651 81692162576103773896923977)
    ·
      refine ⟨61269121932077830422692983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81692162576103773896923977 61269121932077830422692983)
      ·
        refine ⟨91903682898116745634039475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61269121932077830422692983 91903682898116745634039475)
        ·
          refine ⟨137855524347175118451059213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91903682898116745634039475 137855524347175118451059213)
          ·
            refine ⟨51695821630190669419147205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137855524347175118451059213 51695821630190669419147205)
            ·
              refine ⟨9692966555660750516090101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51695821630190669419147205 9692966555660750516090101)
              ·
                refine ⟨908715614593195360883447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9692966555660750516090101 908715614593195360883447)
                ·
                  refine ⟨1363073421889793041325171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 908715614593195360883447 1363073421889793041325171)
                  ·
                    refine ⟨2044610132834689561987757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1363073421889793041325171 2044610132834689561987757)
                    ·
                      refine ⟨766728799813008585745409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2044610132834689561987757 766728799813008585745409)
                      ·
                        rfl

theorem cell23_1493199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 5, 1, 1, 3].length) (baseStart_1493199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1493199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1493199 prefixEnd_1493199 := by exact prefixLift 1493199
  have htrace : WordTrace (prefixWord ++ tailWord_1493199) baseStart_1493199 baseEnd_1493199 := by
    simpa [prefixWord, tailWord_1493199, baseEnd_1493199] using wordTrace_append hprefix tailTrace_1493199
  have hstable : (prefixWord ++ tailWord_1493199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493199).length < 2 ^ (prefixWord ++ tailWord_1493199).sum := by decide
  have hdescent : baseEnd_1493199 < baseStart_1493199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493242 : List Nat := [3, 1, 1, 1, 1, 5, 2, 1, 3, 2, 3]
def baseStart_1493242 : Nat := 118140960795 + 1493242 * 2 ^ 59
def prefixEnd_1493242 : Nat := 4983230072969 + 3 ^ 40 * 1493242 * 2
def baseEnd_1493242 : Nat := 766750879481151917507711

theorem tailTrace_1493242 : CollatzResearch.WordTrace tailWord_1493242 prefixEnd_1493242 766750879481151917507711 := by
  unfold tailWord_1493242
  simp only [CollatzResearch.WordTrace]
  refine ⟨13615752514061683568774495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36308673370831156183398653 13615752514061683568774495)
  ·
    refine ⟨20423628771092525353161743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13615752514061683568774495 20423628771092525353161743)
    ·
      refine ⟨30635443156638788029742615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20423628771092525353161743 30635443156638788029742615)
      ·
        refine ⟨45953164734958182044613923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30635443156638788029742615 45953164734958182044613923)
        ·
          refine ⟨68929747102437273066920885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45953164734958182044613923 68929747102437273066920885)
          ·
            refine ⟨6462163790853494350023833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68929747102437273066920885 6462163790853494350023833)
            ·
              refine ⟨4846622843140120762517875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6462163790853494350023833 4846622843140120762517875)
              ·
                refine ⟨7269934264710181143776813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4846622843140120762517875 7269934264710181143776813)
                ·
                  refine ⟨2726225349266317928916305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7269934264710181143776813 2726225349266317928916305)
                  ·
                    refine ⟨2044669011949738446687229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2726225349266317928916305 2044669011949738446687229)
                    ·
                      refine ⟨766750879481151917507711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2044669011949738446687229 766750879481151917507711)
                      ·
                        rfl

theorem cell23_1493242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 3, 2, 3].length) (baseStart_1493242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1493242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1493242 prefixEnd_1493242 := by exact prefixLift 1493242
  have htrace : WordTrace (prefixWord ++ tailWord_1493242) baseStart_1493242 baseEnd_1493242 := by
    simpa [prefixWord, tailWord_1493242, baseEnd_1493242] using wordTrace_append hprefix tailTrace_1493242
  have hstable : (prefixWord ++ tailWord_1493242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493242).length < 2 ^ (prefixWord ++ tailWord_1493242).sum := by decide
  have hdescent : baseEnd_1493242 < baseStart_1493242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493256 : List Nat := [2, 1, 3, 2, 3, 3, 2, 1, 1, 1, 4]
def baseStart_1493256 : Nat := 118140960795 + 1493256 * 2 ^ 59
def prefixEnd_1493256 : Nat := 4983230072969 + 3 ^ 40 * 1493256 * 2
def baseEnd_1493256 : Nat := 766758068210314862732647

theorem tailTrace_1493256 : CollatzResearch.WordTrace tailWord_1493256 prefixEnd_1493256 766758068210314862732647 := by
  unfold tailWord_1493256
  simp only [CollatzResearch.WordTrace]
  refine ⟨27231760339098007333053811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36309013785464009777405081 27231760339098007333053811)
  ·
    refine ⟨40847640508647010999580717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27231760339098007333053811 40847640508647010999580717)
    ·
      refine ⟨15317865190742629124842769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40847640508647010999580717 15317865190742629124842769)
      ·
        refine ⟨11488398893056971843632077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15317865190742629124842769 11488398893056971843632077)
        ·
          refine ⟨4308149584896364441362029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11488398893056971843632077 4308149584896364441362029)
          ·
            refine ⟨1615556094336136665510761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4308149584896364441362029 1615556094336136665510761)
            ·
              refine ⟨1211667070752102499133071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1615556094336136665510761 1211667070752102499133071)
              ·
                refine ⟨1817500606128153748699607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1211667070752102499133071 1817500606128153748699607)
                ·
                  refine ⟨2726250909192230623049411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1817500606128153748699607 2726250909192230623049411)
                  ·
                    refine ⟨4089376363788345934574117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2726250909192230623049411 4089376363788345934574117)
                    ·
                      refine ⟨766758068210314862732647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4089376363788345934574117 766758068210314862732647)
                      ·
                        rfl

theorem cell23_1493256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 2, 1, 1, 1, 4].length) (baseStart_1493256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1493256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1493256 prefixEnd_1493256 := by exact prefixLift 1493256
  have htrace : WordTrace (prefixWord ++ tailWord_1493256) baseStart_1493256 baseEnd_1493256 := by
    simpa [prefixWord, tailWord_1493256, baseEnd_1493256] using wordTrace_append hprefix tailTrace_1493256
  have hstable : (prefixWord ++ tailWord_1493256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493256).length < 2 ^ (prefixWord ++ tailWord_1493256).sum := by decide
  have hdescent : baseEnd_1493256 < baseStart_1493256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493293 : List Nat := [1, 5, 3, 1, 2, 1, 2, 2, 1, 2, 3]
def baseStart_1493293 : Nat := 118140960795 + 1493293 * 2 ^ 59
def prefixEnd_1493293 : Nat := 4983230072969 + 3 ^ 40 * 1493293 * 2
def baseEnd_1493293 : Nat := 766777066994531217969977

theorem tailTrace_1493293 : CollatzResearch.WordTrace tailWord_1493293 prefixEnd_1493293 766777066994531217969977 := by
  unfold tailWord_1493293
  simp only [CollatzResearch.WordTrace]
  refine ⟨54464870179061969985204533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36309913452707979990136355 54464870179061969985204533)
  ·
    refine ⟨5106081579287059686112925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54464870179061969985204533 5106081579287059686112925)
    ·
      refine ⟨1914780592232647382292347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5106081579287059686112925 1914780592232647382292347)
      ·
        refine ⟨2872170888348971073438521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1914780592232647382292347 2872170888348971073438521)
        ·
          refine ⟨2154128166261728305078891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2872170888348971073438521 2154128166261728305078891)
          ·
            refine ⟨3231192249392592457618337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2154128166261728305078891 3231192249392592457618337)
            ·
              refine ⟨2423394187044444343213753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3231192249392592457618337 2423394187044444343213753)
              ·
                refine ⟨1817545640283333257410315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2423394187044444343213753 1817545640283333257410315)
                ·
                  refine ⟨2726318460424999886115473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1817545640283333257410315 2726318460424999886115473)
                  ·
                    refine ⟨2044738845318749914586605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2726318460424999886115473 2044738845318749914586605)
                    ·
                      refine ⟨766777066994531217969977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2044738845318749914586605 766777066994531217969977)
                      ·
                        rfl

theorem cell23_1493293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_1493293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1493293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1493293 prefixEnd_1493293 := by exact prefixLift 1493293
  have htrace : WordTrace (prefixWord ++ tailWord_1493293) baseStart_1493293 baseEnd_1493293 := by
    simpa [prefixWord, tailWord_1493293, baseEnd_1493293] using wordTrace_append hprefix tailTrace_1493293
  have hstable : (prefixWord ++ tailWord_1493293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493293).length < 2 ^ (prefixWord ++ tailWord_1493293).sum := by decide
  have hdescent : baseEnd_1493293 < baseStart_1493293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493295 : List Nat := [1, 1, 2, 1, 2, 1, 4, 2, 2, 3, 4]
def baseStart_1493295 : Nat := 118140960795 + 1493295 * 2 ^ 59
def prefixEnd_1493295 : Nat := 4983230072969 + 3 ^ 40 * 1493295 * 2
def baseEnd_1493295 : Nat := 766778093955840210144967

theorem tailTrace_1493295 : CollatzResearch.WordTrace tailWord_1493295 prefixEnd_1493295 766778093955840210144967 := by
  unfold tailWord_1493295
  simp only [CollatzResearch.WordTrace]
  refine ⟨54464943125054724326777339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36309962083369816217851559 54464943125054724326777339)
  ·
    refine ⟨81697414687582086490166009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54464943125054724326777339 81697414687582086490166009)
    ·
      refine ⟨61273061015686564867624507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81697414687582086490166009 61273061015686564867624507)
      ·
        refine ⟨91909591523529847301436761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61273061015686564867624507 91909591523529847301436761)
        ·
          refine ⟨68932193642647385476077571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91909591523529847301436761 68932193642647385476077571)
          ·
            refine ⟨103398290463971078214116357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68932193642647385476077571 103398290463971078214116357)
            ·
              refine ⟨19387179461994577165146817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 103398290463971078214116357 19387179461994577165146817)
              ·
                refine ⟨14540384596495932873860113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19387179461994577165146817 14540384596495932873860113)
                ·
                  refine ⟨10905288447371949655395085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14540384596495932873860113 10905288447371949655395085)
                  ·
                    refine ⟨4089483167764481120773157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10905288447371949655395085 4089483167764481120773157)
                    ·
                      refine ⟨766778093955840210144967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4089483167764481120773157 766778093955840210144967)
                      ·
                        rfl

theorem cell23_1493295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 3, 4].length) (baseStart_1493295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1493295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1493295 prefixEnd_1493295 := by exact prefixLift 1493295
  have htrace : WordTrace (prefixWord ++ tailWord_1493295) baseStart_1493295 baseEnd_1493295 := by
    simpa [prefixWord, tailWord_1493295, baseEnd_1493295] using wordTrace_append hprefix tailTrace_1493295
  have hstable : (prefixWord ++ tailWord_1493295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493295).length < 2 ^ (prefixWord ++ tailWord_1493295).sum := by decide
  have hdescent : baseEnd_1493295 < baseStart_1493295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493315 : List Nat := [1, 1, 1, 3, 1, 3, 3, 1, 1, 3, 5]
def baseStart_1493315 : Nat := 118140960795 + 1493315 * 2 ^ 59
def prefixEnd_1493315 : Nat := 4983230072969 + 3 ^ 40 * 1493315 * 2
def baseEnd_1493315 : Nat := 766788363568930131894875

theorem tailTrace_1493315 : CollatzResearch.WordTrace tailWord_1493315 prefixEnd_1493315 766788363568930131894875 := by
  unfold tailWord_1493315
  simp only [CollatzResearch.WordTrace]
  refine ⟨54465672584982267742505399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36310448389988178495003599 54465672584982267742505399)
  ·
    refine ⟨81698508877473401613758099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54465672584982267742505399 81698508877473401613758099)
    ·
      refine ⟨122547763316210102420637149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81698508877473401613758099 122547763316210102420637149)
      ·
        refine ⟨45955411243578788407738931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122547763316210102420637149 45955411243578788407738931)
        ·
          refine ⟨68933116865368182611608397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45955411243578788407738931 68933116865368182611608397)
          ·
            refine ⟨25849918824513068479353149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68933116865368182611608397 25849918824513068479353149)
            ·
              refine ⟨9693719559192400679757431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25849918824513068479353149 9693719559192400679757431)
              ·
                refine ⟨14540579338788601019636147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9693719559192400679757431 14540579338788601019636147)
                ·
                  refine ⟨21810869008182901529454221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14540579338788601019636147 21810869008182901529454221)
                  ·
                    refine ⟨8179075878068588073545333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21810869008182901529454221 8179075878068588073545333)
                    ·
                      refine ⟨766788363568930131894875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8179075878068588073545333 766788363568930131894875)
                      ·
                        rfl

theorem cell23_1493315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 3, 5].length) (baseStart_1493315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1493315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1493315 prefixEnd_1493315 := by exact prefixLift 1493315
  have htrace : WordTrace (prefixWord ++ tailWord_1493315) baseStart_1493315 baseEnd_1493315 := by
    simpa [prefixWord, tailWord_1493315, baseEnd_1493315] using wordTrace_append hprefix tailTrace_1493315
  have hstable : (prefixWord ++ tailWord_1493315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493315).length < 2 ^ (prefixWord ++ tailWord_1493315).sum := by decide
  have hdescent : baseEnd_1493315 < baseStart_1493315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493375 : List Nat := [1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 7]
def baseStart_1493375 : Nat := 118140960795 + 1493375 * 2 ^ 59
def prefixEnd_1493375 : Nat := 4983230072969 + 3 ^ 40 * 1493375 * 2
def baseEnd_1493375 : Nat := 766819172408199897144599

theorem tailTrace_1493375 : CollatzResearch.WordTrace tailWord_1493375 prefixEnd_1493375 766819172408199897144599 := by
  unfold tailWord_1493375
  simp only [CollatzResearch.WordTrace]
  refine ⟨54467860964764897989689579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36311907309843265326459719 54467860964764897989689579)
  ·
    refine ⟨81701791447147346984534369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54467860964764897989689579 81701791447147346984534369)
    ·
      refine ⟨61276343585360510238400777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81701791447147346984534369 61276343585360510238400777)
      ·
        refine ⟨45957257689020382678800583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61276343585360510238400777 45957257689020382678800583)
        ·
          refine ⟨68935886533530574018200875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45957257689020382678800583 68935886533530574018200875)
          ·
            refine ⟨103403829800295861027301313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68935886533530574018200875 103403829800295861027301313)
            ·
              refine ⟨77552872350221895770475985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103403829800295861027301313 77552872350221895770475985)
              ·
                refine ⟨58164654262666421827856989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77552872350221895770475985 58164654262666421827856989)
                ·
                  refine ⟨21811745348499908185446371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58164654262666421827856989 21811745348499908185446371)
                  ·
                    refine ⟨32717618022749862278169557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21811745348499908185446371 32717618022749862278169557)
                    ·
                      refine ⟨766819172408199897144599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 32717618022749862278169557 766819172408199897144599)
                      ·
                        rfl

theorem cell23_1493375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 7].length) (baseStart_1493375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1493375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1493375 prefixEnd_1493375 := by exact prefixLift 1493375
  have htrace : WordTrace (prefixWord ++ tailWord_1493375) baseStart_1493375 baseEnd_1493375 := by
    simpa [prefixWord, tailWord_1493375, baseEnd_1493375] using wordTrace_append hprefix tailTrace_1493375
  have hstable : (prefixWord ++ tailWord_1493375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493375).length < 2 ^ (prefixWord ++ tailWord_1493375).sum := by decide
  have hdescent : baseEnd_1493375 < baseStart_1493375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493396 : List Nat := [2, 4, 2, 1, 3, 1, 1, 1, 2, 3, 3]
def baseStart_1493396 : Nat := 118140960795 + 1493396 * 2 ^ 59
def prefixEnd_1493396 : Nat := 4983230072969 + 3 ^ 40 * 1493396 * 2
def baseEnd_1493396 : Nat := 766829955501944314982003

theorem tailTrace_1493396 : CollatzResearch.WordTrace tailWord_1493396 prefixEnd_1493396 766829955501944314982003 := by
  unfold tailWord_1493396
  simp only [CollatzResearch.WordTrace]
  refine ⟨27234313448844409288102021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36312417931792545717469361 27234313448844409288102021)
  ·
    refine ⟨5106433771658326741519129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27234313448844409288102021 5106433771658326741519129)
    ·
      refine ⟨3829825328743745056139347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5106433771658326741519129 3829825328743745056139347)
      ·
        refine ⟨5744737993115617584209021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3829825328743745056139347 5744737993115617584209021)
        ·
          refine ⟨2154276747418356594078383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5744737993115617584209021 2154276747418356594078383)
          ·
            refine ⟨3231415121127534891117575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2154276747418356594078383 3231415121127534891117575)
            ·
              refine ⟨4847122681691302336676363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3231415121127534891117575 4847122681691302336676363)
              ·
                refine ⟨7270684022536953505014545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4847122681691302336676363 7270684022536953505014545)
                ·
                  refine ⟨5453013016902715128760909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7270684022536953505014545 5453013016902715128760909)
                  ·
                    refine ⟨2044879881338518173285341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5453013016902715128760909 2044879881338518173285341)
                    ·
                      refine ⟨766829955501944314982003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2044879881338518173285341 766829955501944314982003)
                      ·
                        rfl

theorem cell23_1493396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_1493396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1493396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1493396 prefixEnd_1493396 := by exact prefixLift 1493396
  have htrace : WordTrace (prefixWord ++ tailWord_1493396) baseStart_1493396 baseEnd_1493396 := by
    simpa [prefixWord, tailWord_1493396, baseEnd_1493396] using wordTrace_append hprefix tailTrace_1493396
  have hstable : (prefixWord ++ tailWord_1493396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493396).length < 2 ^ (prefixWord ++ tailWord_1493396).sum := by decide
  have hdescent : baseEnd_1493396 < baseStart_1493396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493416 : List Nat := [2, 1, 6, 1, 1, 1, 3, 1, 2, 5]
def baseStart_1493416 : Nat := 118140960795 + 1493416 * 2 ^ 59
def prefixEnd_1493416 : Nat := 4983230072969 + 3 ^ 40 * 1493416 * 2
def baseEnd_1493416 : Nat := 255613408371678078910637

theorem tailTrace_1493416 : CollatzResearch.WordTrace tailWord_1493416 prefixEnd_1493416 255613408371678078910637 := by
  unfold tailWord_1493416
  simp only [CollatzResearch.WordTrace]
  refine ⟨27234678178808180995966051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36312904238410907994621401 27234678178808180995966051)
  ·
    refine ⟨40852017268212271493949077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27234678178808180995966051 40852017268212271493949077)
    ·
      refine ⟨1914938309447450226278863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 40852017268212271493949077 1914938309447450226278863)
      ·
        refine ⟨2872407464171175339418295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1914938309447450226278863 2872407464171175339418295)
        ·
          refine ⟨4308611196256763009127443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2872407464171175339418295 4308611196256763009127443)
          ·
            refine ⟨6462916794385144513691165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4308611196256763009127443 6462916794385144513691165)
            ·
              refine ⟨2423593797894429192634187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6462916794385144513691165 2423593797894429192634187)
              ·
                refine ⟨3635390696841643788951281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2423593797894429192634187 3635390696841643788951281)
                ·
                  refine ⟨2726543022631232841713461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3635390696841643788951281 2726543022631232841713461)
                  ·
                    refine ⟨255613408371678078910637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2726543022631232841713461 255613408371678078910637)
                    ·
                      rfl

theorem cell23_1493416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_1493416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1493416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1493416 prefixEnd_1493416 := by exact prefixLift 1493416
  have htrace : WordTrace (prefixWord ++ tailWord_1493416) baseStart_1493416 baseEnd_1493416 := by
    simpa [prefixWord, tailWord_1493416, baseEnd_1493416] using wordTrace_append hprefix tailTrace_1493416
  have hstable : (prefixWord ++ tailWord_1493416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493416).length < 2 ^ (prefixWord ++ tailWord_1493416).sum := by decide
  have hdescent : baseEnd_1493416 < baseStart_1493416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493436 : List Nat := [2, 2, 2, 4, 1, 1, 1, 2, 2, 4, 2]
def baseStart_1493436 : Nat := 118140960795 + 1493436 * 2 ^ 59
def prefixEnd_1493436 : Nat := 4983230072969 + 3 ^ 40 * 1493436 * 2
def baseEnd_1493436 : Nat := 766850494728124158481819

theorem tailTrace_1493436 : CollatzResearch.WordTrace tailWord_1493436 prefixEnd_1493436 766850494728124158481819 := by
  unfold tailWord_1493436
  simp only [CollatzResearch.WordTrace]
  refine ⟨27235042908771952703830081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36313390545029270271773441 27235042908771952703830081)
  ·
    refine ⟨20426282181578964527872561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27235042908771952703830081 20426282181578964527872561)
    ·
      refine ⟨15319711636184223395904421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20426282181578964527872561 15319711636184223395904421)
      ·
        refine ⟨2872445931784541886732079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15319711636184223395904421 2872445931784541886732079)
        ·
          refine ⟨4308668897676812830098119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2872445931784541886732079 4308668897676812830098119)
          ·
            refine ⟨6463003346515219245147179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4308668897676812830098119 6463003346515219245147179)
            ·
              refine ⟨9694505019772828867720769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6463003346515219245147179 9694505019772828867720769)
              ·
                refine ⟨7270878764829621650790577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9694505019772828867720769 7270878764829621650790577)
                ·
                  refine ⟨5453159073622216238092933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7270878764829621650790577 5453159073622216238092933)
                  ·
                    refine ⟨1022467326304165544642425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5453159073622216238092933 1022467326304165544642425)
                    ·
                      refine ⟨766850494728124158481819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1022467326304165544642425 766850494728124158481819)
                      ·
                        rfl

theorem cell23_1493436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_1493436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1493436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1493436 prefixEnd_1493436 := by exact prefixLift 1493436
  have htrace : WordTrace (prefixWord ++ tailWord_1493436) baseStart_1493436 baseEnd_1493436 := by
    simpa [prefixWord, tailWord_1493436, baseEnd_1493436] using wordTrace_append hprefix tailTrace_1493436
  have hstable : (prefixWord ++ tailWord_1493436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493436).length < 2 ^ (prefixWord ++ tailWord_1493436).sum := by decide
  have hdescent : baseEnd_1493436 < baseStart_1493436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493469 : List Nat := [1, 4, 3, 1, 1, 1, 1, 1, 2, 5, 3]
def baseStart_1493469 : Nat := 118140960795 + 1493469 * 2 ^ 59
def prefixEnd_1493469 : Nat := 4983230072969 + 3 ^ 40 * 1493469 * 2
def baseEnd_1493469 : Nat := 766867439589722529369167

theorem tailTrace_1493469 : CollatzResearch.WordTrace tailWord_1493469 prefixEnd_1493469 766867439589722529369167 := by
  unfold tailWord_1493469
  simp only [CollatzResearch.WordTrace]
  refine ⟨54471289426424352043611461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36314192950949568029074307 54471289426424352043611461)
  ·
    refine ⟨10213366767454566008177149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54471289426424352043611461 10213366767454566008177149)
    ·
      refine ⟨3830012537795462253066431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10213366767454566008177149 3830012537795462253066431)
      ·
        refine ⟨5745018806693193379599647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3830012537795462253066431 5745018806693193379599647)
        ·
          refine ⟨8617528210039790069399471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5745018806693193379599647 8617528210039790069399471)
          ·
            refine ⟨12926292315059685104099207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8617528210039790069399471 12926292315059685104099207)
            ·
              refine ⟨19389438472589527656148811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12926292315059685104099207 19389438472589527656148811)
              ·
                refine ⟨29084157708884291484223217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19389438472589527656148811 29084157708884291484223217)
                ·
                  refine ⟨21813118281663218613167413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29084157708884291484223217 21813118281663218613167413)
                  ·
                    refine ⟨2044979838905926744984445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21813118281663218613167413 2044979838905926744984445)
                    ·
                      refine ⟨766867439589722529369167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2044979838905926744984445 766867439589722529369167)
                      ·
                        rfl

theorem cell23_1493469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_1493469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1493469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1493469 prefixEnd_1493469 := by exact prefixLift 1493469
  have htrace : WordTrace (prefixWord ++ tailWord_1493469) baseStart_1493469 baseEnd_1493469 := by
    simpa [prefixWord, tailWord_1493469, baseEnd_1493469] using wordTrace_append hprefix tailTrace_1493469
  have hstable : (prefixWord ++ tailWord_1493469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493469).length < 2 ^ (prefixWord ++ tailWord_1493469).sum := by decide
  have hdescent : baseEnd_1493469 < baseStart_1493469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493489 : List Nat := [1, 2, 2, 2, 3, 1, 1, 5, 1, 5]
def baseStart_1493489 : Nat := 118140960795 + 1493489 * 2 ^ 59
def prefixEnd_1493489 : Nat := 4983230072969 + 3 ^ 40 * 1493489 * 2
def baseEnd_1493489 : Nat := 255625903067604150373025

theorem tailTrace_1493489 : CollatzResearch.WordTrace tailWord_1493489 prefixEnd_1493489 255625903067604150373025 := by
  unfold tailWord_1493489
  simp only [CollatzResearch.WordTrace]
  refine ⟨54472018886351895459339521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36314679257567930306226347 54472018886351895459339521)
  ·
    refine ⟨40854014164763921594504641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54472018886351895459339521 40854014164763921594504641)
    ·
      refine ⟨30640510623572941195878481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40854014164763921594504641 30640510623572941195878481)
      ·
        refine ⟨22980382967679705896908861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30640510623572941195878481 22980382967679705896908861)
        ·
          refine ⟨8617643612879889711340823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22980382967679705896908861 8617643612879889711340823)
          ·
            refine ⟨12926465419319834567011235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8617643612879889711340823 12926465419319834567011235)
            ·
              refine ⟨19389698128979751850516853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12926465419319834567011235 19389698128979751850516853)
              ·
                refine ⟨1817784199591851735985955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19389698128979751850516853 1817784199591851735985955)
                ·
                  refine ⟨2726676299387777603978933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1817784199591851735985955 2726676299387777603978933)
                  ·
                    refine ⟨255625903067604150373025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2726676299387777603978933 255625903067604150373025)
                    ·
                      rfl

theorem cell23_1493489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 5, 1, 5].length) (baseStart_1493489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1493489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1493489 prefixEnd_1493489 := by exact prefixLift 1493489
  have htrace : WordTrace (prefixWord ++ tailWord_1493489) baseStart_1493489 baseEnd_1493489 := by
    simpa [prefixWord, tailWord_1493489, baseEnd_1493489] using wordTrace_append hprefix tailTrace_1493489
  have hstable : (prefixWord ++ tailWord_1493489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493489).length < 2 ^ (prefixWord ++ tailWord_1493489).sum := by decide
  have hdescent : baseEnd_1493489 < baseStart_1493489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493496 : List Nat := [2, 1, 2, 1, 1, 4, 3, 2, 2, 3, 2]
def baseStart_1493496 : Nat := 118140960795 + 1493496 * 2 ^ 59
def prefixEnd_1493496 : Nat := 4983230072969 + 3 ^ 40 * 1493496 * 2
def baseEnd_1493496 : Nat := 766881303567393923731543

theorem tailTrace_1493496 : CollatzResearch.WordTrace tailWord_1493496 prefixEnd_1493496 766881303567393923731543 := by
  unfold tailWord_1493496
  simp only [CollatzResearch.WordTrace]
  refine ⟨27236137098663267827422171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36314849464884357103229561 27236137098663267827422171)
  ·
    refine ⟨40854205647994901741133257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27236137098663267827422171 40854205647994901741133257)
    ·
      refine ⟨30640654235996176305849943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40854205647994901741133257 30640654235996176305849943)
      ·
        refine ⟨45960981353994264458774915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30640654235996176305849943 45960981353994264458774915)
        ·
          refine ⟨68941472030991396688162373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45960981353994264458774915 68941472030991396688162373)
          ·
            refine ⟨12926526005810886879030445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68941472030991396688162373 12926526005810886879030445)
            ·
              refine ⟨4847447252179082579636417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12926526005810886879030445 4847447252179082579636417)
              ·
                refine ⟨3635585439134311934727313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4847447252179082579636417 3635585439134311934727313)
                ·
                  refine ⟨2726689079350733951045485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3635585439134311934727313 2726689079350733951045485)
                  ·
                    refine ⟨1022508404756525231642057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2726689079350733951045485 1022508404756525231642057)
                    ·
                      refine ⟨766881303567393923731543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1022508404756525231642057 766881303567393923731543)
                      ·
                        rfl

theorem cell23_1493496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 2, 2, 3, 2].length) (baseStart_1493496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1493496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1493496 prefixEnd_1493496 := by exact prefixLift 1493496
  have htrace : WordTrace (prefixWord ++ tailWord_1493496) baseStart_1493496 baseEnd_1493496 := by
    simpa [prefixWord, tailWord_1493496, baseEnd_1493496] using wordTrace_append hprefix tailTrace_1493496
  have hstable : (prefixWord ++ tailWord_1493496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493496).length < 2 ^ (prefixWord ++ tailWord_1493496).sum := by decide
  have hdescent : baseEnd_1493496 < baseStart_1493496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493510 : List Nat := [6, 2, 1, 1, 1, 2, 1, 3, 6]
def baseStart_1493510 : Nat := 118140960795 + 1493510 * 2 ^ 59
def prefixEnd_1493510 : Nat := 4983230072969 + 3 ^ 40 * 1493510 * 2
def baseEnd_1493510 : Nat := 85209832477395207661831

theorem tailTrace_1493510 : CollatzResearch.WordTrace tailWord_1493510 prefixEnd_1493510 85209832477395207661831 := by
  unfold tailWord_1493510
  simp only [CollatzResearch.WordTrace]
  refine ⟨1702274525602369251432937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 36315189879517210697235989 1702274525602369251432937)
  ·
    refine ⟨1276705894201776938574703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1702274525602369251432937 1276705894201776938574703)
    ·
      refine ⟨1915058841302665407862055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1276705894201776938574703 1915058841302665407862055)
      ·
        refine ⟨2872588261953998111793083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1915058841302665407862055 2872588261953998111793083)
        ·
          refine ⟨4308882392930997167689625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2872588261953998111793083 4308882392930997167689625)
          ·
            refine ⟨3231661794698247875767219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4308882392930997167689625 3231661794698247875767219)
            ·
              refine ⟨4847492692047371813650829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3231661794698247875767219 4847492692047371813650829)
              ·
                refine ⟨1817809759517764430119061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4847492692047371813650829 1817809759517764430119061)
                ·
                  refine ⟨85209832477395207661831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1817809759517764430119061 85209832477395207661831)
                  ·
                    rfl

theorem cell23_1493510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_1493510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1493510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1493510 prefixEnd_1493510 := by exact prefixLift 1493510
  have htrace : WordTrace (prefixWord ++ tailWord_1493510) baseStart_1493510 baseEnd_1493510 := by
    simpa [prefixWord, tailWord_1493510, baseEnd_1493510] using wordTrace_append hprefix tailTrace_1493510
  have hstable : (prefixWord ++ tailWord_1493510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493510).length < 2 ^ (prefixWord ++ tailWord_1493510).sum := by decide
  have hdescent : baseEnd_1493510 < baseStart_1493510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493529 : List Nat := [1, 2, 1, 2, 1, 1, 2, 5, 3, 2, 3]
def baseStart_1493529 : Nat := 118140960795 + 1493529 * 2 ^ 59
def prefixEnd_1493529 : Nat := 4983230072969 + 3 ^ 40 * 1493529 * 2
def baseEnd_1493529 : Nat := 766898248428992294618891

theorem tailTrace_1493529 : CollatzResearch.WordTrace tailWord_1493529 prefixEnd_1493529 766898248428992294618891 := by
  unfold tailWord_1493529
  simp only [CollatzResearch.WordTrace]
  refine ⟨54473477806206982290795641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36315651870804654860530427 54473477806206982290795641)
  ·
    refine ⟨40855108354655236718096731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54473477806206982290795641 40855108354655236718096731)
    ·
      refine ⟨61282662531982855077145097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40855108354655236718096731 61282662531982855077145097)
      ·
        refine ⟨45961996898987141307858823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61282662531982855077145097 45961996898987141307858823)
        ·
          refine ⟨68942995348480711961788235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45961996898987141307858823 68942995348480711961788235)
          ·
            refine ⟨103414493022721067942682353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68942995348480711961788235 103414493022721067942682353)
            ·
              refine ⟨77560869767040800957011765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103414493022721067942682353 77560869767040800957011765)
              ·
                refine ⟨7271331540660075089719853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77560869767040800957011765 7271331540660075089719853)
                ·
                  refine ⟨2726749327747528158644945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7271331540660075089719853 2726749327747528158644945)
                  ·
                    refine ⟨2045061995810646118983709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2726749327747528158644945 2045061995810646118983709)
                    ·
                      refine ⟨766898248428992294618891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2045061995810646118983709 766898248428992294618891)
                      ·
                        rfl

theorem cell23_1493529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 3, 2, 3].length) (baseStart_1493529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1493529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1493529 prefixEnd_1493529 := by exact prefixLift 1493529
  have htrace : WordTrace (prefixWord ++ tailWord_1493529) baseStart_1493529 baseEnd_1493529 := by
    simpa [prefixWord, tailWord_1493529, baseEnd_1493529] using wordTrace_append hprefix tailTrace_1493529
  have hstable : (prefixWord ++ tailWord_1493529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493529).length < 2 ^ (prefixWord ++ tailWord_1493529).sum := by decide
  have hdescent : baseEnd_1493529 < baseStart_1493529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493536 : List Nat := [2, 1, 1, 6, 2, 1, 1, 2, 1, 6]
def baseStart_1493536 : Nat := 118140960795 + 1493536 * 2 ^ 59
def prefixEnd_1493536 : Nat := 4983230072969 + 3 ^ 40 * 1493536 * 2
def baseEnd_1493536 : Nat := 255633947597857922410453

theorem tailTrace_1493536 : CollatzResearch.WordTrace tailWord_1493536 prefixEnd_1493536 255633947597857922410453 := by
  unfold tailWord_1493536
  simp only [CollatzResearch.WordTrace]
  refine ⟨27236866558590811243150231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36315822078121081657533641 27236866558590811243150231)
  ·
    refine ⟨40855299837886216864725347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27236866558590811243150231 40855299837886216864725347)
    ·
      refine ⟨61282949756829325297088021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40855299837886216864725347 61282949756829325297088021)
      ·
        refine ⟨2872638269851374623301001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 61282949756829325297088021 2872638269851374623301001)
        ·
          refine ⟨2154478702388530967475751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2872638269851374623301001 2154478702388530967475751)
          ·
            refine ⟨3231718053582796451213627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2154478702388530967475751 3231718053582796451213627)
            ·
              refine ⟨4847577080374194676820441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3231718053582796451213627 4847577080374194676820441)
              ·
                refine ⟨3635682810280646007615331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4847577080374194676820441 3635682810280646007615331)
                ·
                  refine ⟨5453524215420969011422997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3635682810280646007615331 5453524215420969011422997)
                  ·
                    refine ⟨255633947597857922410453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5453524215420969011422997 255633947597857922410453)
                    ·
                      rfl

theorem cell23_1493536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 2, 1, 6].length) (baseStart_1493536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1493536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1493536 prefixEnd_1493536 := by exact prefixLift 1493536
  have htrace : WordTrace (prefixWord ++ tailWord_1493536) baseStart_1493536 baseEnd_1493536 := by
    simpa [prefixWord, tailWord_1493536, baseEnd_1493536] using wordTrace_append hprefix tailTrace_1493536
  have hstable : (prefixWord ++ tailWord_1493536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493536).length < 2 ^ (prefixWord ++ tailWord_1493536).sum := by decide
  have hdescent : baseEnd_1493536 < baseStart_1493536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493539 : List Nat := [1, 1, 1, 4, 4, 1, 1, 1, 3, 2, 4]
def baseStart_1493539 : Nat := 118140960795 + 1493539 * 2 ^ 59
def prefixEnd_1493539 : Nat := 4983230072969 + 3 ^ 40 * 1493539 * 2
def baseEnd_1493539 : Nat := 766903383235537255493845

theorem tailTrace_1493539 : CollatzResearch.WordTrace tailWord_1493539 prefixEnd_1493539 766903383235537255493845 := by
  unfold tailWord_1493539
  simp only [CollatzResearch.WordTrace]
  refine ⟨54473842536170753998659671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36315895024113835999106447 54473842536170753998659671)
  ·
    refine ⟨81710763804256130997989507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54473842536170753998659671 81710763804256130997989507)
    ·
      refine ⟨122566145706384196496984261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81710763804256130997989507 122566145706384196496984261)
      ·
        refine ⟨22981152319947036843184549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122566145706384196496984261 22981152319947036843184549)
        ·
          refine ⟨4308966059990069408097103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22981152319947036843184549 4308966059990069408097103)
          ·
            refine ⟨6463449089985104112145655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4308966059990069408097103 6463449089985104112145655)
            ·
              refine ⟨9695173634977656168218483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6463449089985104112145655 9695173634977656168218483)
              ·
                refine ⟨14542760452466484252327725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9695173634977656168218483 14542760452466484252327725)
                ·
                  refine ⟨5453535169674931594622897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14542760452466484252327725 5453535169674931594622897)
                  ·
                    refine ⟨4090151377256198695967173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5453535169674931594622897 4090151377256198695967173)
                    ·
                      refine ⟨766903383235537255493845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4090151377256198695967173 766903383235537255493845)
                      ·
                        rfl

theorem cell23_1493539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 3, 2, 4].length) (baseStart_1493539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1493539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1493539 prefixEnd_1493539 := by exact prefixLift 1493539
  have htrace : WordTrace (prefixWord ++ tailWord_1493539) baseStart_1493539 baseEnd_1493539 := by
    simpa [prefixWord, tailWord_1493539, baseEnd_1493539] using wordTrace_append hprefix tailTrace_1493539
  have hstable : (prefixWord ++ tailWord_1493539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493539).length < 2 ^ (prefixWord ++ tailWord_1493539).sum := by decide
  have hdescent : baseEnd_1493539 < baseStart_1493539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493540 : List Nat := [2, 3, 1, 5, 1, 1, 3, 1, 1, 5]
def baseStart_1493540 : Nat := 118140960795 + 1493540 * 2 ^ 59
def prefixEnd_1493540 : Nat := 4983230072969 + 3 ^ 40 * 1493540 * 2
def baseEnd_1493540 : Nat := 255634632238730583860447

theorem tailTrace_1493540 : CollatzResearch.WordTrace tailWord_1493540 prefixEnd_1493540 255634632238730583860447 := by
  unfold tailWord_1493540
  simp only [CollatzResearch.WordTrace]
  refine ⟨27236939504583565584723037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36315919339444754112964049 27236939504583565584723037)
  ·
    refine ⟨10213852314218837094271139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27236939504583565584723037 10213852314218837094271139)
    ·
      refine ⟨15320778471328255641406709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10213852314218837094271139 15320778471328255641406709)
      ·
        refine ⟨1436322981687023966381879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15320778471328255641406709 1436322981687023966381879)
        ·
          refine ⟨2154484472530535949572819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1436322981687023966381879 2154484472530535949572819)
          ·
            refine ⟨3231726708795803924359229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2154484472530535949572819 3231726708795803924359229)
            ·
              refine ⟨1211897515798426471634711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3231726708795803924359229 1211897515798426471634711)
              ·
                refine ⟨1817846273697639707452067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1211897515798426471634711 1817846273697639707452067)
                ·
                  refine ⟨2726769410546459561178101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1817846273697639707452067 2726769410546459561178101)
                  ·
                    refine ⟨255634632238730583860447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2726769410546459561178101 255634632238730583860447)
                    ·
                      rfl

theorem cell23_1493540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 3, 1, 1, 5].length) (baseStart_1493540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1493540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1493540 prefixEnd_1493540 := by exact prefixLift 1493540
  have htrace : WordTrace (prefixWord ++ tailWord_1493540) baseStart_1493540 baseEnd_1493540 := by
    simpa [prefixWord, tailWord_1493540, baseEnd_1493540] using wordTrace_append hprefix tailTrace_1493540
  have hstable : (prefixWord ++ tailWord_1493540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493540).length < 2 ^ (prefixWord ++ tailWord_1493540).sum := by decide
  have hdescent : baseEnd_1493540 < baseStart_1493540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493546 : List Nat := [3, 1, 4, 1, 1, 2, 3, 1, 1, 1, 5]
def baseStart_1493546 : Nat := 118140960795 + 1493546 * 2 ^ 59
def prefixEnd_1493546 : Nat := 4983230072969 + 3 ^ 40 * 1493546 * 2
def baseEnd_1493546 : Nat := 766906977600118728106313

theorem tailTrace_1493546 : CollatzResearch.WordTrace tailWord_1493546 prefixEnd_1493546 766906977600118728106313 := by
  unfold tailWord_1493546
  simp only [CollatzResearch.WordTrace]
  refine ⟨13618524461786348548541123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36316065231430262796109661 13618524461786348548541123)
  ·
    refine ⟨20427786692679522822811685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13618524461786348548541123 20427786692679522822811685)
    ·
      refine ⟨3830210004877410529277191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20427786692679522822811685 3830210004877410529277191)
      ·
        refine ⟨5745315007316115793915787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3830210004877410529277191 5745315007316115793915787)
        ·
          refine ⟨8617972510974173690873681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5745315007316115793915787 8617972510974173690873681)
          ·
            refine ⟨6463479383230630268155261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8617972510974173690873681 6463479383230630268155261)
            ·
              refine ⟨2423804768711486350558223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6463479383230630268155261 2423804768711486350558223)
              ·
                refine ⟨3635707153067229525837335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2423804768711486350558223 3635707153067229525837335)
                ·
                  refine ⟨5453560729600844288756003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3635707153067229525837335 5453560729600844288756003)
                  ·
                    refine ⟨8180341094401266433134005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5453560729600844288756003 8180341094401266433134005)
                    ·
                      refine ⟨766906977600118728106313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8180341094401266433134005 766906977600118728106313)
                      ·
                        rfl

theorem cell23_1493546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_1493546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1493546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1493546 prefixEnd_1493546 := by exact prefixLift 1493546
  have htrace : WordTrace (prefixWord ++ tailWord_1493546) baseStart_1493546 baseEnd_1493546 := by
    simpa [prefixWord, tailWord_1493546, baseEnd_1493546] using wordTrace_append hprefix tailTrace_1493546
  have hstable : (prefixWord ++ tailWord_1493546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493546).length < 2 ^ (prefixWord ++ tailWord_1493546).sum := by decide
  have hdescent : baseEnd_1493546 < baseStart_1493546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493559 : List Nat := [1, 1, 3, 1, 2, 3, 1, 2, 3, 3, 3]
def baseStart_1493559 : Nat := 118140960795 + 1493559 * 2 ^ 59
def prefixEnd_1493559 : Nat := 4983230072969 + 3 ^ 40 * 1493559 * 2
def baseEnd_1493559 : Nat := 766913652848627177243753

theorem tailTrace_1493559 : CollatzResearch.WordTrace tailWord_1493559 prefixEnd_1493559 766913652848627177243753 := by
  unfold tailWord_1493559
  simp only [CollatzResearch.WordTrace]
  refine ⟨54474571996098297414387731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36316381330732198276258487 54474571996098297414387731)
  ·
    refine ⟨81711857994147446121581597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54474571996098297414387731 81711857994147446121581597)
    ·
      refine ⟨30641946747805292295593099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81711857994147446121581597 30641946747805292295593099)
      ·
        refine ⟨45962920121707938443389649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30641946747805292295593099 45962920121707938443389649)
        ·
          refine ⟨34472190091280953832542237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45962920121707938443389649 34472190091280953832542237)
          ·
            refine ⟨12927071284230357687203339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34472190091280953832542237 12927071284230357687203339)
            ·
              refine ⟨19390606926345536530805009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12927071284230357687203339 19390606926345536530805009)
              ·
                refine ⟨14542955194759152398103757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19390606926345536530805009 14542955194759152398103757)
                ·
                  refine ⟨5453608198034682149288909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14542955194759152398103757 5453608198034682149288909)
                  ·
                    refine ⟨2045103074263005805983341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5453608198034682149288909 2045103074263005805983341)
                    ·
                      refine ⟨766913652848627177243753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2045103074263005805983341 766913652848627177243753)
                      ·
                        rfl

theorem cell23_1493559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 3, 3, 3].length) (baseStart_1493559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1493559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1493559 prefixEnd_1493559 := by exact prefixLift 1493559
  have htrace : WordTrace (prefixWord ++ tailWord_1493559) baseStart_1493559 baseEnd_1493559 := by
    simpa [prefixWord, tailWord_1493559, baseEnd_1493559] using wordTrace_append hprefix tailTrace_1493559
  have hstable : (prefixWord ++ tailWord_1493559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493559).length < 2 ^ (prefixWord ++ tailWord_1493559).sum := by decide
  have hdescent : baseEnd_1493559 < baseStart_1493559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493560 : List Nat := [2, 1, 2, 1, 4, 1, 3, 4, 1, 2, 2]
def baseStart_1493560 : Nat := 118140960795 + 1493560 * 2 ^ 59
def prefixEnd_1493560 : Nat := 4983230072969 + 3 ^ 40 * 1493560 * 2
def baseEnd_1493560 : Nat := 766914166329281673331249

theorem tailTrace_1493560 : CollatzResearch.WordTrace tailWord_1493560 prefixEnd_1493560 766914166329281673331249 := by
  unfold tailWord_1493560
  simp only [CollatzResearch.WordTrace]
  refine ⟨27237304234547337292587067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36316405646063116390116089 27237304234547337292587067)
  ·
    refine ⟨40855956351821005938880601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27237304234547337292587067 40855956351821005938880601)
    ·
      refine ⟨30641967263865754454160451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40855956351821005938880601 30641967263865754454160451)
      ·
        refine ⟨45962950895798631681240677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30641967263865754454160451 45962950895798631681240677)
        ·
          refine ⟨8618053292962243440232627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45962950895798631681240677 8618053292962243440232627)
          ·
            refine ⟨12927079939443365160348941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8618053292962243440232627 12927079939443365160348941)
            ·
              refine ⟨4847654977291261935130853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12927079939443365160348941 4847654977291261935130853)
              ·
                refine ⟨908935308242111612837035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4847654977291261935130853 908935308242111612837035)
                ·
                  refine ⟨1363402962363167419255553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 908935308242111612837035 1363402962363167419255553)
                  ·
                    refine ⟨1022552221772375564441665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1363402962363167419255553 1022552221772375564441665)
                    ·
                      refine ⟨766914166329281673331249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1022552221772375564441665 766914166329281673331249)
                      ·
                        rfl

theorem cell23_1493560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 4, 1, 2, 2].length) (baseStart_1493560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1493560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1493560 prefixEnd_1493560 := by exact prefixLift 1493560
  have htrace : WordTrace (prefixWord ++ tailWord_1493560) baseStart_1493560 baseEnd_1493560 := by
    simpa [prefixWord, tailWord_1493560, baseEnd_1493560] using wordTrace_append hprefix tailTrace_1493560
  have hstable : (prefixWord ++ tailWord_1493560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493560).length < 2 ^ (prefixWord ++ tailWord_1493560).sum := by decide
  have hdescent : baseEnd_1493560 < baseStart_1493560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493603 : List Nat := [1, 1, 1, 5, 1, 2, 3, 3, 1, 3, 2]
def baseStart_1493603 : Nat := 118140960795 + 1493603 * 2 ^ 59
def prefixEnd_1493603 : Nat := 4983230072969 + 3 ^ 40 * 1493603 * 2
def baseEnd_1493603 : Nat := 766936245997425005093551

theorem tailTrace_1493603 : CollatzResearch.WordTrace tailWord_1493603 prefixEnd_1493603 766936245997425005093551 := by
  unfold tailWord_1493603
  simp only [CollatzResearch.WordTrace]
  refine ⟨54476176807938892928989463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36317451205292595285992975 54476176807938892928989463)
  ·
    refine ⟨81714265211908339393484195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54476176807938892928989463 81714265211908339393484195)
    ·
      refine ⟨122571397817862509090226293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81714265211908339393484195 122571397817862509090226293)
      ·
        refine ⟨11491068545424610227208715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 122571397817862509090226293 11491068545424610227208715)
        ·
          refine ⟨17236602818136915340813073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11491068545424610227208715 17236602818136915340813073)
          ·
            refine ⟨12927452113602686505609805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17236602818136915340813073 12927452113602686505609805)
            ·
              refine ⟨4847794542601007439603677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12927452113602686505609805 4847794542601007439603677)
              ·
                refine ⟨1817922953475377789851379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4847794542601007439603677 1817922953475377789851379)
                ·
                  refine ⟨2726884430213066684777069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1817922953475377789851379 2726884430213066684777069)
                  ·
                    refine ⟨1022581661329900006791401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2726884430213066684777069 1022581661329900006791401)
                    ·
                      refine ⟨766936245997425005093551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1022581661329900006791401 766936245997425005093551)
                      ·
                        rfl

theorem cell23_1493603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 3, 1, 3, 2].length) (baseStart_1493603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1493603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1493603 prefixEnd_1493603 := by exact prefixLift 1493603
  have htrace : WordTrace (prefixWord ++ tailWord_1493603) baseStart_1493603 baseEnd_1493603 := by
    simpa [prefixWord, tailWord_1493603, baseEnd_1493603] using wordTrace_append hprefix tailTrace_1493603
  have hstable : (prefixWord ++ tailWord_1493603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493603).length < 2 ^ (prefixWord ++ tailWord_1493603).sum := by decide
  have hdescent : baseEnd_1493603 < baseStart_1493603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493619 : List Nat := [1, 1, 1, 2, 2, 1, 1, 5, 2, 4, 3]
def baseStart_1493619 : Nat := 118140960795 + 1493619 * 2 ^ 59
def prefixEnd_1493619 : Nat := 4983230072969 + 3 ^ 40 * 1493619 * 2
def baseEnd_1493619 : Nat := 766944461687896942493477

theorem tailTrace_1493619 : CollatzResearch.WordTrace tailWord_1493619 prefixEnd_1493619 766944461687896942493477 := by
  unfold tailWord_1493619
  simp only [CollatzResearch.WordTrace]
  refine ⟨54476760375880927661571911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36317840250587285107714607 54476760375880927661571911)
  ·
    refine ⟨81715140563821391492357867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54476760375880927661571911 81715140563821391492357867)
    ·
      refine ⟨122572710845732087238536801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81715140563821391492357867 122572710845732087238536801)
      ·
        refine ⟨91929533134299065428902601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122572710845732087238536801 91929533134299065428902601)
        ·
          refine ⟨68947149850724299071676951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91929533134299065428902601 68947149850724299071676951)
          ·
            refine ⟨103420724776086448607515427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68947149850724299071676951 103420724776086448607515427)
            ·
              refine ⟨155131087164129672911273141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103420724776086448607515427 155131087164129672911273141)
              ·
                refine ⟨14543539421637156835431857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 155131087164129672911273141 14543539421637156835431857)
                ·
                  refine ⟨10907654566227867626573893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14543539421637156835431857 10907654566227867626573893)
                  ·
                    refine ⟨2045185231167725179982605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10907654566227867626573893 2045185231167725179982605)
                    ·
                      refine ⟨766944461687896942493477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2045185231167725179982605 766944461687896942493477)
                      ·
                        rfl

theorem cell23_1493619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 4, 3].length) (baseStart_1493619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1493619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1493619 prefixEnd_1493619 := by exact prefixLift 1493619
  have htrace : WordTrace (prefixWord ++ tailWord_1493619) baseStart_1493619 baseEnd_1493619 := by
    simpa [prefixWord, tailWord_1493619, baseEnd_1493619] using wordTrace_append hprefix tailTrace_1493619
  have hstable : (prefixWord ++ tailWord_1493619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493619).length < 2 ^ (prefixWord ++ tailWord_1493619).sum := by decide
  have hdescent : baseEnd_1493619 < baseStart_1493619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493634 : List Nat := [3, 4, 3, 1, 2, 1, 2, 7]
def baseStart_1493634 : Nat := 118140960795 + 1493634 * 2 ^ 59
def prefixEnd_1493634 : Nat := 4983230072969 + 3 ^ 40 * 1493634 * 2
def baseEnd_1493634 : Nat := 28405635699915347548367

theorem tailTrace_1493634 : CollatzResearch.WordTrace tailWord_1493634 prefixEnd_1493634 28405635699915347548367 := by
  unfold tailWord_1493634
  simp only [CollatzResearch.WordTrace]
  refine ⟨13619326867706646305841989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36318204980551056815578637 13619326867706646305841989)
  ·
    refine ⟨2553623787694996182345373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13619326867706646305841989 2553623787694996182345373)
    ·
      refine ⟨957608920385623568379515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2553623787694996182345373 957608920385623568379515)
      ·
        refine ⟨1436413380578435352569273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 957608920385623568379515 1436413380578435352569273)
        ·
          refine ⟨1077310035433826514426955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1436413380578435352569273 1077310035433826514426955)
          ·
            refine ⟨1615965053150739771640433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1077310035433826514426955 1615965053150739771640433)
            ·
              refine ⟨1211973789863054828730325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1615965053150739771640433 1211973789863054828730325)
              ·
                refine ⟨28405635699915347548367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1211973789863054828730325 28405635699915347548367)
                ·
                  rfl

theorem cell23_1493634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 2, 7].length) (baseStart_1493634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1493634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1493634 prefixEnd_1493634 := by exact prefixLift 1493634
  have htrace : WordTrace (prefixWord ++ tailWord_1493634) baseStart_1493634 baseEnd_1493634 := by
    simpa [prefixWord, tailWord_1493634, baseEnd_1493634] using wordTrace_append hprefix tailTrace_1493634
  have hstable : (prefixWord ++ tailWord_1493634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493634).length < 2 ^ (prefixWord ++ tailWord_1493634).sum := by decide
  have hdescent : baseEnd_1493634 < baseStart_1493634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493639 : List Nat := [1, 1, 4, 2, 1, 2, 1, 4, 7]
def baseStart_1493639 : Nat := 118140960795 + 1493639 * 2 ^ 59
def prefixEnd_1493639 : Nat := 4983230072969 + 3 ^ 40 * 1493639 * 2
def baseEnd_1493639 : Nat := 85217192366776318249265

theorem tailTrace_1493639 : CollatzResearch.WordTrace tailWord_1493639 prefixEnd_1493639 85217192366776318249265 := by
  unfold tailWord_1493639
  simp only [CollatzResearch.WordTrace]
  refine ⟨54477489835808471077299971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36318326557205647384866647 54477489835808471077299971)
  ·
    refine ⟨81716234753712706615949957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54477489835808471077299971 81716234753712706615949957)
    ·
      refine ⟨15321794016321132490490617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81716234753712706615949957 15321794016321132490490617)
      ·
        refine ⟨11491345512240849367867963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15321794016321132490490617 11491345512240849367867963)
        ·
          refine ⟨17237018268361274051801945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11491345512240849367867963 17237018268361274051801945)
          ·
            refine ⟨12927763701270955538851459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17237018268361274051801945 12927763701270955538851459)
            ·
              refine ⟨19391645551906433308277189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12927763701270955538851459 19391645551906433308277189)
              ·
                refine ⟨3635933540982456245301973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19391645551906433308277189 3635933540982456245301973)
                ·
                  refine ⟨85217192366776318249265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3635933540982456245301973 85217192366776318249265)
                  ·
                    rfl

theorem cell23_1493639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 4, 7].length) (baseStart_1493639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1493639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1493639 prefixEnd_1493639 := by exact prefixLift 1493639
  have htrace : WordTrace (prefixWord ++ tailWord_1493639) baseStart_1493639 baseEnd_1493639 := by
    simpa [prefixWord, tailWord_1493639, baseEnd_1493639] using wordTrace_append hprefix tailTrace_1493639
  have hstable : (prefixWord ++ tailWord_1493639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493639).length < 2 ^ (prefixWord ++ tailWord_1493639).sum := by decide
  have hdescent : baseEnd_1493639 < baseStart_1493639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493650 : List Nat := [3, 2, 3, 1, 2, 1, 1, 2, 4, 2, 2]
def baseStart_1493650 : Nat := 118140960795 + 1493650 * 2 ^ 59
def prefixEnd_1493650 : Nat := 4983230072969 + 3 ^ 40 * 1493650 * 2
def baseEnd_1493650 : Nat := 766960379588186321205835

theorem tailTrace_1493650 : CollatzResearch.WordTrace tailWord_1493650 prefixEnd_1493650 766960379588186321205835 := by
  unfold tailWord_1493650
  simp only [CollatzResearch.WordTrace]
  refine ⟨13619472759692154988987601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36318594025845746637300269 13619472759692154988987601)
  ·
    refine ⟨10214604569769116241740701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13619472759692154988987601 10214604569769116241740701)
    ·
      refine ⟨3830476713663418590652763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10214604569769116241740701 3830476713663418590652763)
      ·
        refine ⟨5745715070495127885979145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3830476713663418590652763 5745715070495127885979145)
        ·
          refine ⟨4309286302871345914484359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5745715070495127885979145 4309286302871345914484359)
          ·
            refine ⟨6463929454307018871726539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4309286302871345914484359 6463929454307018871726539)
            ·
              refine ⟨9695894181460528307589809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6463929454307018871726539 9695894181460528307589809)
              ·
                refine ⟨7271920636095396230692357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9695894181460528307589809 7271920636095396230692357)
                ·
                  refine ⟨1363485119267886793254817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7271920636095396230692357 1363485119267886793254817)
                  ·
                    refine ⟨1022613839450915094941113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1363485119267886793254817 1022613839450915094941113)
                    ·
                      refine ⟨766960379588186321205835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1022613839450915094941113 766960379588186321205835)
                      ·
                        rfl

theorem cell23_1493650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 4, 2, 2].length) (baseStart_1493650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1493650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1493650 prefixEnd_1493650 := by exact prefixLift 1493650
  have htrace : WordTrace (prefixWord ++ tailWord_1493650) baseStart_1493650 baseEnd_1493650 := by
    simpa [prefixWord, tailWord_1493650, baseEnd_1493650] using wordTrace_append hprefix tailTrace_1493650
  have hstable : (prefixWord ++ tailWord_1493650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493650).length < 2 ^ (prefixWord ++ tailWord_1493650).sum := by decide
  have hdescent : baseEnd_1493650 < baseStart_1493650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493679 : List Nat := [1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 7]
def baseStart_1493679 : Nat := 118140960795 + 1493679 * 2 ^ 59
def prefixEnd_1493679 : Nat := 4983230072969 + 3 ^ 40 * 1493679 * 2
def baseEnd_1493679 : Nat := 766975270527166707743201

theorem tailTrace_1493679 : CollatzResearch.WordTrace tailWord_1493679 prefixEnd_1493679 766975270527166707743201 := by
  unfold tailWord_1493679
  simp only [CollatzResearch.WordTrace]
  refine ⟨54478948755663557908756091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36319299170442371939170727 54478948755663557908756091)
  ·
    refine ⟨81718423133495336863134137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54478948755663557908756091 81718423133495336863134137)
    ·
      refine ⟨61288817350121502647350603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81718423133495336863134137 61288817350121502647350603)
      ·
        refine ⟨91933226025182253971025905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61288817350121502647350603 91933226025182253971025905)
        ·
          refine ⟨68949919518886690478269429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91933226025182253971025905 68949919518886690478269429)
          ·
            refine ⟨6464054954895627232337759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68949919518886690478269429 6464054954895627232337759)
            ·
              refine ⟨9696082432343440848506639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6464054954895627232337759 9696082432343440848506639)
              ·
                refine ⟨14544123648515161272759959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9696082432343440848506639 14544123648515161272759959)
                ·
                  refine ⟨21816185472772741909139939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14544123648515161272759959 21816185472772741909139939)
                  ·
                    refine ⟨32724278209159112863709909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21816185472772741909139939 32724278209159112863709909)
                    ·
                      refine ⟨766975270527166707743201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 32724278209159112863709909 766975270527166707743201)
                      ·
                        rfl

theorem cell23_1493679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 7].length) (baseStart_1493679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1493679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1493679 prefixEnd_1493679 := by exact prefixLift 1493679
  have htrace : WordTrace (prefixWord ++ tailWord_1493679) baseStart_1493679 baseEnd_1493679 := by
    simpa [prefixWord, tailWord_1493679, baseEnd_1493679] using wordTrace_append hprefix tailTrace_1493679
  have hstable : (prefixWord ++ tailWord_1493679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493679).length < 2 ^ (prefixWord ++ tailWord_1493679).sum := by decide
  have hdescent : baseEnd_1493679 < baseStart_1493679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493767 : List Nat := [1, 1, 4, 4, 1, 2, 2, 3, 1, 4]
def baseStart_1493767 : Nat := 118140960795 + 1493767 * 2 ^ 59
def prefixEnd_1493767 : Nat := 4983230072969 + 3 ^ 40 * 1493767 * 2
def baseEnd_1493767 : Nat := 255673485608254121147599

theorem tailTrace_1493767 : CollatzResearch.WordTrace tailWord_1493767 prefixEnd_1493767 255673485608254121147599 := by
  unfold tailWord_1493767
  simp only [CollatzResearch.WordTrace]
  refine ⟨54482158379344748937959555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36321438919563165958639703 54482158379344748937959555)
  ·
    refine ⟨81723237569017123406939333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54482158379344748937959555 81723237569017123406939333)
    ·
      refine ⟨15323107044190710638801125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81723237569017123406939333 15323107044190710638801125)
      ·
        refine ⟨2873082570785758244775211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15323107044190710638801125 2873082570785758244775211)
        ·
          refine ⟨4309623856178637367162817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2873082570785758244775211 4309623856178637367162817)
          ·
            refine ⟨3232217892133978025372113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4309623856178637367162817 3232217892133978025372113)
            ·
              refine ⟨2424163419100483519029085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3232217892133978025372113 2424163419100483519029085)
              ·
                refine ⟨909061282162681319635907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2424163419100483519029085 909061282162681319635907)
                ·
                  refine ⟨1363591923244021979453861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 909061282162681319635907 1363591923244021979453861)
                  ·
                    refine ⟨255673485608254121147599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1363591923244021979453861 255673485608254121147599)
                    ·
                      rfl

theorem cell23_1493767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 3, 1, 4].length) (baseStart_1493767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1493767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1493767 prefixEnd_1493767 := by exact prefixLift 1493767
  have htrace : WordTrace (prefixWord ++ tailWord_1493767) baseStart_1493767 baseEnd_1493767 := by
    simpa [prefixWord, tailWord_1493767, baseEnd_1493767] using wordTrace_append hprefix tailTrace_1493767
  have hstable : (prefixWord ++ tailWord_1493767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493767).length < 2 ^ (prefixWord ++ tailWord_1493767).sum := by decide
  have hdescent : baseEnd_1493767 < baseStart_1493767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493816 : List Nat := [2, 1, 2, 1, 3, 2, 1, 2, 3, 1, 5]
def baseStart_1493816 : Nat := 118140960795 + 1493816 * 2 ^ 59
def prefixEnd_1493816 : Nat := 4983230072969 + 3 ^ 40 * 1493816 * 2
def baseEnd_1493816 : Nat := 767045617376832671730071

theorem tailTrace_1493816 : CollatzResearch.WordTrace tailWord_1493816 prefixEnd_1493816 767045617376832671730071 := by
  unfold tailWord_1493816
  simp only [CollatzResearch.WordTrace]
  refine ⟨27241972778083615153246651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36322630370778153537662201 27241972778083615153246651)
  ·
    refine ⟨40862959167125422729869977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27241972778083615153246651 40862959167125422729869977)
    ·
      refine ⟨30647219375344067047402483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40862959167125422729869977 30647219375344067047402483)
      ·
        refine ⟨45970829063016100571103725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30647219375344067047402483 45970829063016100571103725)
        ·
          refine ⟨17239060898631037714163897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45970829063016100571103725 17239060898631037714163897)
          ·
            refine ⟨12929295673973278285622923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17239060898631037714163897 12929295673973278285622923)
            ·
              refine ⟨19393943510959917428434385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12929295673973278285622923 19393943510959917428434385)
              ·
                refine ⟨14545457633219938071325789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19393943510959917428434385 14545457633219938071325789)
                ·
                  refine ⟨5454546612457476776747171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14545457633219938071325789 5454546612457476776747171)
                  ·
                    refine ⟨8181819918686215165120757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5454546612457476776747171 8181819918686215165120757)
                    ·
                      refine ⟨767045617376832671730071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8181819918686215165120757 767045617376832671730071)
                      ·
                        rfl

theorem cell23_1493816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 3, 1, 5].length) (baseStart_1493816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1493816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1493816 prefixEnd_1493816 := by exact prefixLift 1493816
  have htrace : WordTrace (prefixWord ++ tailWord_1493816) baseStart_1493816 baseEnd_1493816 := by
    simpa [prefixWord, tailWord_1493816, baseEnd_1493816] using wordTrace_append hprefix tailTrace_1493816
  have hstable : (prefixWord ++ tailWord_1493816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493816).length < 2 ^ (prefixWord ++ tailWord_1493816).sum := by decide
  have hdescent : baseEnd_1493816 < baseStart_1493816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493823 : List Nat := [1, 1, 2, 2, 5, 1, 1, 2, 4, 4]
def baseStart_1493823 : Nat := 118140960795 + 1493823 * 2 ^ 59
def prefixEnd_1493823 : Nat := 4983230072969 + 3 ^ 40 * 1493823 * 2
def baseEnd_1493823 : Nat := 255683070580471381447513

theorem tailTrace_1493823 : CollatzResearch.WordTrace tailWord_1493823 prefixEnd_1493823 255683070580471381447513 := by
  unfold tailWord_1493823
  simp only [CollatzResearch.WordTrace]
  refine ⟨54484200867141870501998123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36322800578094580334665415 54484200867141870501998123)
  ·
    refine ⟨81726301300712805752997185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54484200867141870501998123 81726301300712805752997185)
    ·
      refine ⟨61294725975534604314747889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81726301300712805752997185 61294725975534604314747889)
      ·
        refine ⟨45971044481650953236060917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61294725975534604314747889 45971044481650953236060917)
        ·
          refine ⟨4309785420154776865880711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45971044481650953236060917 4309785420154776865880711)
          ·
            refine ⟨6464678130232165298821067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4309785420154776865880711 6464678130232165298821067)
            ·
              refine ⟨9697017195348247948231601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6464678130232165298821067 9697017195348247948231601)
              ·
                refine ⟨7272762896511185961173701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9697017195348247948231601 7272762896511185961173701)
                ·
                  refine ⟨1363643043095847367720069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7272762896511185961173701 1363643043095847367720069)
                  ·
                    refine ⟨255683070580471381447513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1363643043095847367720069 255683070580471381447513)
                    ·
                      rfl

theorem cell23_1493823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 4, 4].length) (baseStart_1493823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1493823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1493823 prefixEnd_1493823 := by exact prefixLift 1493823
  have htrace : WordTrace (prefixWord ++ tailWord_1493823) baseStart_1493823 baseEnd_1493823 := by
    simpa [prefixWord, tailWord_1493823, baseEnd_1493823] using wordTrace_append hprefix tailTrace_1493823
  have hstable : (prefixWord ++ tailWord_1493823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493823).length < 2 ^ (prefixWord ++ tailWord_1493823).sum := by decide
  have hdescent : baseEnd_1493823 < baseStart_1493823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493833 : List Nat := [1, 2, 1, 1, 2, 6, 2, 1, 1, 1, 5]
def baseStart_1493833 : Nat := 118140960795 + 1493833 * 2 ^ 59
def prefixEnd_1493833 : Nat := 4983230072969 + 3 ^ 40 * 1493833 * 2
def baseEnd_1493833 : Nat := 767054346547959105217493

theorem tailTrace_1493833 : CollatzResearch.WordTrace tailWord_1493833 prefixEnd_1493833 767054346547959105217493 := by
  unfold tailWord_1493833
  simp only [CollatzResearch.WordTrace]
  refine ⟨54484565597105642209862153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36323043731403761473241435 54484565597105642209862153)
  ·
    refine ⟨40863424197829231657396615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54484565597105642209862153 40863424197829231657396615)
    ·
      refine ⟨61295136296743847486094923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40863424197829231657396615 61295136296743847486094923)
      ·
        refine ⟨91942704445115771229142385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61295136296743847486094923 91942704445115771229142385)
        ·
          refine ⟨68957028333836828421856789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91942704445115771229142385 68957028333836828421856789)
          ·
            refine ⟨3232360703148601332274537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 68957028333836828421856789 3232360703148601332274537)
            ·
              refine ⟨2424270527361450999205903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3232360703148601332274537 2424270527361450999205903)
              ·
                refine ⟨3636405791042176498808855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2424270527361450999205903 3636405791042176498808855)
                ·
                  refine ⟨5454608686563264748213283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3636405791042176498808855 5454608686563264748213283)
                  ·
                    refine ⟨8181913029844897122319925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5454608686563264748213283 8181913029844897122319925)
                    ·
                      refine ⟨767054346547959105217493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8181913029844897122319925 767054346547959105217493)
                      ·
                        rfl

theorem cell23_1493833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 1, 1, 1, 5].length) (baseStart_1493833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1493833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1493833 prefixEnd_1493833 := by exact prefixLift 1493833
  have htrace : WordTrace (prefixWord ++ tailWord_1493833) baseStart_1493833 baseEnd_1493833 := by
    simpa [prefixWord, tailWord_1493833, baseEnd_1493833] using wordTrace_append hprefix tailTrace_1493833
  have hstable : (prefixWord ++ tailWord_1493833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493833).length < 2 ^ (prefixWord ++ tailWord_1493833).sum := by decide
  have hdescent : baseEnd_1493833 < baseStart_1493833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493836 : List Nat := [2, 2, 1, 3, 3, 1, 11]
def baseStart_1493836 : Nat := 118140960795 + 1493836 * 2 ^ 59
def prefixEnd_1493836 : Nat := 4983230072969 + 3 ^ 40 * 1493836 * 2
def baseEnd_1493836 : Nat := 9469825765307686339259

theorem tailTrace_1493836 : CollatzResearch.WordTrace tailWord_1493836 prefixEnd_1493836 9469825765307686339259 := by
  unfold tailWord_1493836
  simp only [CollatzResearch.WordTrace]
  refine ⟨27242337508047386861110681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36323116677396515814814241 27242337508047386861110681)
  ·
    refine ⟨20431753131035540145833011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27242337508047386861110681 20431753131035540145833011)
    ·
      refine ⟨30647629696553310218749517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20431753131035540145833011 30647629696553310218749517)
      ·
        refine ⟨11492861136207491332031069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30647629696553310218749517 11492861136207491332031069)
        ·
          refine ⟨4309822926077809249511651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11492861136207491332031069 4309822926077809249511651)
          ·
            refine ⟨6464734389116713874267477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4309822926077809249511651 6464734389116713874267477)
            ·
              refine ⟨9469825765307686339259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 6464734389116713874267477 9469825765307686339259)
              ·
                rfl

theorem cell23_1493836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 11].length) (baseStart_1493836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1493836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1493836 prefixEnd_1493836 := by exact prefixLift 1493836
  have htrace : WordTrace (prefixWord ++ tailWord_1493836) baseStart_1493836 baseEnd_1493836 := by
    simpa [prefixWord, tailWord_1493836, baseEnd_1493836] using wordTrace_append hprefix tailTrace_1493836
  have hstable : (prefixWord ++ tailWord_1493836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493836).length < 2 ^ (prefixWord ++ tailWord_1493836).sum := by decide
  have hdescent : baseEnd_1493836 < baseStart_1493836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493847 : List Nat := [1, 1, 3, 2, 4, 1, 3, 1, 3, 2, 2]
def baseStart_1493847 : Nat := 118140960795 + 1493847 * 2 ^ 59
def prefixEnd_1493847 : Nat := 4983230072969 + 3 ^ 40 * 1493847 * 2
def baseEnd_1493847 : Nat := 767061535277122050442429

theorem tailTrace_1493847 : CollatzResearch.WordTrace tailWord_1493847 prefixEnd_1493847 767061535277122050442429 := by
  unfold tailWord_1493847
  simp only [CollatzResearch.WordTrace]
  refine ⟨54485076219054922600871795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36323384146036615067247863 54485076219054922600871795)
  ·
    refine ⟨81727614328582383901307693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54485076219054922600871795 81727614328582383901307693)
    ·
      refine ⟨30647855373218393962990385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81727614328582383901307693 30647855373218393962990385)
      ·
        refine ⟨22985891529913795472242789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30647855373218393962990385 22985891529913795472242789)
        ·
          refine ⟨4309854661858836651045523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22985891529913795472242789 4309854661858836651045523)
          ·
            refine ⟨6464781992788254976568285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4309854661858836651045523 6464781992788254976568285)
            ·
              refine ⟨2424293247295595616213107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6464781992788254976568285 2424293247295595616213107)
              ·
                refine ⟨3636439870943393424319661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2424293247295595616213107 3636439870943393424319661)
                ·
                  refine ⟨1363664951603772534119873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3636439870943393424319661 1363664951603772534119873)
                  ·
                    refine ⟨1022748713702829400589905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1363664951603772534119873 1022748713702829400589905)
                    ·
                      refine ⟨767061535277122050442429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1022748713702829400589905 767061535277122050442429)
                      ·
                        rfl

theorem cell23_1493847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 1, 3, 2, 2].length) (baseStart_1493847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1493847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1493847 prefixEnd_1493847 := by exact prefixLift 1493847
  have htrace : WordTrace (prefixWord ++ tailWord_1493847) baseStart_1493847 baseEnd_1493847 := by
    simpa [prefixWord, tailWord_1493847, baseEnd_1493847] using wordTrace_append hprefix tailTrace_1493847
  have hstable : (prefixWord ++ tailWord_1493847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493847).length < 2 ^ (prefixWord ++ tailWord_1493847).sum := by decide
  have hdescent : baseEnd_1493847 < baseStart_1493847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493856 : List Nat := [2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 6]
def baseStart_1493856 : Nat := 118140960795 + 1493856 * 2 ^ 59
def prefixEnd_1493856 : Nat := 4983230072969 + 3 ^ 40 * 1493856 * 2
def baseEnd_1493856 : Nat := 767066156603012515229887

theorem tailTrace_1493856 : CollatzResearch.WordTrace tailWord_1493856 prefixEnd_1493856 767066156603012515229887 := by
  unfold tailWord_1493856
  simp only [CollatzResearch.WordTrace]
  refine ⟨27242702238011158568974711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36323602984014878091966281 27242702238011158568974711)
  ·
    refine ⟨40864053357016737853462067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27242702238011158568974711 40864053357016737853462067)
    ·
      refine ⟨61296080035525106780193101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40864053357016737853462067 61296080035525106780193101)
      ·
        refine ⟨22986030013321915042572413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61296080035525106780193101 22986030013321915042572413)
        ·
          refine ⟨8619761254995718140964655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22986030013321915042572413 8619761254995718140964655)
          ·
            refine ⟨12929641882493577211446983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8619761254995718140964655 12929641882493577211446983)
            ·
              refine ⟨19394462823740365817170475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12929641882493577211446983 19394462823740365817170475)
              ·
                refine ⟨29091694235610548725755713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19394462823740365817170475 29091694235610548725755713)
                ·
                  refine ⟨21818770676707911544316785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29091694235610548725755713 21818770676707911544316785)
                  ·
                    refine ⟨16364078007530933658237589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21818770676707911544316785 16364078007530933658237589)
                    ·
                      refine ⟨767066156603012515229887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16364078007530933658237589 767066156603012515229887)
                      ·
                        rfl

theorem cell23_1493856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_1493856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1493856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1493856 prefixEnd_1493856 := by exact prefixLift 1493856
  have htrace : WordTrace (prefixWord ++ tailWord_1493856) baseStart_1493856 baseEnd_1493856 := by
    simpa [prefixWord, tailWord_1493856, baseEnd_1493856] using wordTrace_append hprefix tailTrace_1493856
  have hstable : (prefixWord ++ tailWord_1493856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493856).length < 2 ^ (prefixWord ++ tailWord_1493856).sum := by decide
  have hdescent : baseEnd_1493856 < baseStart_1493856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493897 : List Nat := [1, 2, 1, 1, 5, 3, 2, 2, 2, 1, 3]
def baseStart_1493897 : Nat := 118140960795 + 1493897 * 2 ^ 59
def prefixEnd_1493897 : Nat := 4983230072969 + 3 ^ 40 * 1493897 * 2
def baseEnd_1493897 : Nat := 767087209309846854817199

theorem tailTrace_1493897 : CollatzResearch.WordTrace tailWord_1493897 prefixEnd_1493897 767087209309846854817199 := by
  unfold tailWord_1493897
  simp only [CollatzResearch.WordTrace]
  refine ⟨54486899868873781140191945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36324599912582520760127963 54486899868873781140191945)
  ·
    refine ⟨40865174901655335855143959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54486899868873781140191945 40865174901655335855143959)
    ·
      refine ⟨61297762352483003782715939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40865174901655335855143959 61297762352483003782715939)
      ·
        refine ⟨91946643528724505674073909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61297762352483003782715939 91946643528724505674073909)
        ·
          refine ⟨8619997830817922406944429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 91946643528724505674073909 8619997830817922406944429)
          ·
            refine ⟨3232499186556720902604161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8619997830817922406944429 3232499186556720902604161)
            ·
              refine ⟨2424374389917540676953121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3232499186556720902604161 2424374389917540676953121)
              ·
                refine ⟨1818280792438155507714841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2424374389917540676953121 1818280792438155507714841)
                ·
                  refine ⟨1363710594328616630786131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1818280792438155507714841 1363710594328616630786131)
                  ·
                    refine ⟨2045565891492924946179197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1363710594328616630786131 2045565891492924946179197)
                    ·
                      refine ⟨767087209309846854817199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2045565891492924946179197 767087209309846854817199)
                      ·
                        rfl

theorem cell23_1493897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 2, 2, 1, 3].length) (baseStart_1493897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1493897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1493897 prefixEnd_1493897 := by exact prefixLift 1493897
  have htrace : WordTrace (prefixWord ++ tailWord_1493897) baseStart_1493897 baseEnd_1493897 := by
    simpa [prefixWord, tailWord_1493897, baseEnd_1493897] using wordTrace_append hprefix tailTrace_1493897
  have hstable : (prefixWord ++ tailWord_1493897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493897).length < 2 ^ (prefixWord ++ tailWord_1493897).sum := by decide
  have hdescent : baseEnd_1493897 < baseStart_1493897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493898 : List Nat := [3, 1, 2, 4, 1, 3, 2, 2, 1, 2, 2]
def baseStart_1493898 : Nat := 118140960795 + 1493898 * 2 ^ 59
def prefixEnd_1493898 : Nat := 4983230072969 + 3 ^ 40 * 1493898 * 2
def baseEnd_1493898 : Nat := 767087722790501350904695

theorem tailTrace_1493898 : CollatzResearch.WordTrace tailWord_1493898 prefixEnd_1493898 767087722790501350904695 := by
  unfold tailWord_1493898
  simp only [CollatzResearch.WordTrace]
  refine ⟨13621734085467539577744587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36324624227913438873985565 13621734085467539577744587)
  ·
    refine ⟨20432601128201309366616881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13621734085467539577744587 20432601128201309366616881)
    ·
      refine ⟨15324450846150982024962661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20432601128201309366616881 15324450846150982024962661)
      ·
        refine ⟨2873334533653309129680499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15324450846150982024962661 2873334533653309129680499)
        ·
          refine ⟨4310001800479963694520749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2873334533653309129680499 4310001800479963694520749)
          ·
            refine ⟨1616250675179986385445281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4310001800479963694520749 1616250675179986385445281)
            ·
              refine ⟨1212188006384989789083961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1616250675179986385445281 1212188006384989789083961)
              ·
                refine ⟨909141004788742341812971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1212188006384989789083961 909141004788742341812971)
                ·
                  refine ⟨1363711507183113512719457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 909141004788742341812971 1363711507183113512719457)
                  ·
                    refine ⟨1022783630387335134539593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1363711507183113512719457 1022783630387335134539593)
                    ·
                      refine ⟨767087722790501350904695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1022783630387335134539593 767087722790501350904695)
                      ·
                        rfl

theorem cell23_1493898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_1493898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1493898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1493898 prefixEnd_1493898 := by exact prefixLift 1493898
  have htrace : WordTrace (prefixWord ++ tailWord_1493898) baseStart_1493898 baseEnd_1493898 := by
    simpa [prefixWord, tailWord_1493898, baseEnd_1493898] using wordTrace_append hprefix tailTrace_1493898
  have hstable : (prefixWord ++ tailWord_1493898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493898).length < 2 ^ (prefixWord ++ tailWord_1493898).sum := by decide
  have hdescent : baseEnd_1493898 < baseStart_1493898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493920 : List Nat := [2, 1, 1, 4, 1, 1, 3, 3, 1, 4, 2]
def baseStart_1493920 : Nat := 118140960795 + 1493920 * 2 ^ 59
def prefixEnd_1493920 : Nat := 4983230072969 + 3 ^ 40 * 1493920 * 2
def baseEnd_1493920 : Nat := 767099019364900264829593

theorem tailTrace_1493920 : CollatzResearch.WordTrace tailWord_1493920 prefixEnd_1493920 767099019364900264829593 := by
  unfold tailWord_1493920
  simp only [CollatzResearch.WordTrace]
  refine ⟨27243869373895228034139607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36325159165193637378852809 27243869373895228034139607)
  ·
    refine ⟨40865804060842842051209411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27243869373895228034139607 40865804060842842051209411)
    ·
      refine ⟨61298706091264263076814117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40865804060842842051209411 61298706091264263076814117)
      ·
        refine ⟨11493507392112049326902647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61298706091264263076814117 11493507392112049326902647)
        ·
          refine ⟨17240261088168073990353971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11493507392112049326902647 17240261088168073990353971)
          ·
            refine ⟨25860391632252110985530957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17240261088168073990353971 25860391632252110985530957)
            ·
              refine ⟨9697646862094541619574109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25860391632252110985530957 9697646862094541619574109)
              ·
                refine ⟨3636617573285453107340291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9697646862094541619574109 3636617573285453107340291)
                ·
                  refine ⟨5454926359928179661010437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3636617573285453107340291 5454926359928179661010437)
                  ·
                    refine ⟨1022798692486533686439457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5454926359928179661010437 1022798692486533686439457)
                    ·
                      refine ⟨767099019364900264829593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1022798692486533686439457 767099019364900264829593)
                      ·
                        rfl

theorem cell23_1493920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 3, 1, 4, 2].length) (baseStart_1493920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1493920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1493920 prefixEnd_1493920 := by exact prefixLift 1493920
  have htrace : WordTrace (prefixWord ++ tailWord_1493920) baseStart_1493920 baseEnd_1493920 := by
    simpa [prefixWord, tailWord_1493920, baseEnd_1493920] using wordTrace_append hprefix tailTrace_1493920
  have hstable : (prefixWord ++ tailWord_1493920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493920).length < 2 ^ (prefixWord ++ tailWord_1493920).sum := by decide
  have hdescent : baseEnd_1493920 < baseStart_1493920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493960 : List Nat := [2, 1, 3, 1, 5, 1, 2, 1, 7]
def baseStart_1493960 : Nat := 118140960795 + 1493960 * 2 ^ 59
def prefixEnd_1493960 : Nat := 4983230072969 + 3 ^ 40 * 1493960 * 2
def baseEnd_1493960 : Nat := 85235506510120012036601

theorem tailTrace_1493960 : CollatzResearch.WordTrace tailWord_1493960 prefixEnd_1493960 85235506510120012036601 := by
  unfold tailWord_1493960
  simp only [CollatzResearch.WordTrace]
  refine ⟨27244598833822771449867667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36326131778430361933156889 27244598833822771449867667)
  ·
    refine ⟨40866898250734157174801501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27244598833822771449867667 40866898250734157174801501)
    ·
      refine ⟨15325086844025308940550563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40866898250734157174801501 15325086844025308940550563)
      ·
        refine ⟨22987630266037963410825845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15325086844025308940550563 22987630266037963410825845)
        ·
          refine ⟨2155090337441059069764923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22987630266037963410825845 2155090337441059069764923)
          ·
            refine ⟨3232635506161588604647385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2155090337441059069764923 3232635506161588604647385)
            ·
              refine ⟨2424476629621191453485539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3232635506161588604647385 2424476629621191453485539)
              ·
                refine ⟨3636714944431787180228309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2424476629621191453485539 3636714944431787180228309)
                ·
                  refine ⟨85235506510120012036601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3636714944431787180228309 85235506510120012036601)
                  ·
                    rfl

theorem cell23_1493960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 1, 7].length) (baseStart_1493960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1493960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1493960 prefixEnd_1493960 := by exact prefixLift 1493960
  have htrace : WordTrace (prefixWord ++ tailWord_1493960) baseStart_1493960 baseEnd_1493960 := by
    simpa [prefixWord, tailWord_1493960, baseEnd_1493960] using wordTrace_append hprefix tailTrace_1493960
  have hstable : (prefixWord ++ tailWord_1493960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493960).length < 2 ^ (prefixWord ++ tailWord_1493960).sum := by decide
  have hdescent : baseEnd_1493960 < baseStart_1493960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493965 : List Nat := [1, 6, 3, 1, 1, 1, 3, 1, 2, 1, 3]
def baseStart_1493965 : Nat := 118140960795 + 1493965 * 2 ^ 59
def prefixEnd_1493965 : Nat := 4983230072969 + 3 ^ 40 * 1493965 * 2
def baseEnd_1493965 : Nat := 767122125994352588766887

theorem tailTrace_1493965 : CollatzResearch.WordTrace tailWord_1493965 prefixEnd_1493965 767122125994352588766887 := by
  unfold tailWord_1493965
  simp only [CollatzResearch.WordTrace]
  refine ⟨54489380032627428753667349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36326253355084952502444899 54489380032627428753667349)
  ·
    refine ⟨2554189689029410722828157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 54489380032627428753667349 2554189689029410722828157)
    ·
      refine ⟨957821133386029021060559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2554189689029410722828157 957821133386029021060559)
      ·
        refine ⟨1436731700079043531590839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 957821133386029021060559 1436731700079043531590839)
        ·
          refine ⟨2155097550118565297386259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1436731700079043531590839 2155097550118565297386259)
          ·
            refine ⟨3232646325177847946079389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2155097550118565297386259 3232646325177847946079389)
            ·
              refine ⟨1212242371941692979779771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3232646325177847946079389 1212242371941692979779771)
              ·
                refine ⟨1818363557912539469669657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1212242371941692979779771 1818363557912539469669657)
                ·
                  refine ⟨1363772668434404602252243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1818363557912539469669657 1363772668434404602252243)
                  ·
                    refine ⟨2045659002651606903378365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1363772668434404602252243 2045659002651606903378365)
                    ·
                      refine ⟨767122125994352588766887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2045659002651606903378365 767122125994352588766887)
                      ·
                        rfl

theorem cell23_1493965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_1493965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1493965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1493965 prefixEnd_1493965 := by exact prefixLift 1493965
  have htrace : WordTrace (prefixWord ++ tailWord_1493965) baseStart_1493965 baseEnd_1493965 := by
    simpa [prefixWord, tailWord_1493965, baseEnd_1493965] using wordTrace_append hprefix tailTrace_1493965
  have hstable : (prefixWord ++ tailWord_1493965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493965).length < 2 ^ (prefixWord ++ tailWord_1493965).sum := by decide
  have hdescent : baseEnd_1493965 < baseStart_1493965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1493993 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 8, 1, 4]
def baseStart_1493993 : Nat := 118140960795 + 1493993 * 2 ^ 59
def prefixEnd_1493993 : Nat := 4983230072969 + 3 ^ 40 * 1493993 * 2
def baseEnd_1493993 : Nat := 767136503452678479216757

theorem tailTrace_1493993 : CollatzResearch.WordTrace tailWord_1493993 prefixEnd_1493993 767136503452678479216757 := by
  unfold tailWord_1493993
  simp only [CollatzResearch.WordTrace]
  refine ⟨54490401276525989535686633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36326934184350659690457755 54490401276525989535686633)
  ·
    refine ⟨40867800957394492151764975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54490401276525989535686633 40867800957394492151764975)
    ·
      refine ⟨61301701436091738227647463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40867800957394492151764975 61301701436091738227647463)
      ·
        refine ⟨91952552154137607341471195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61301701436091738227647463 91952552154137607341471195)
        ·
          refine ⟨137928828231206411012206793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91952552154137607341471195 137928828231206411012206793)
          ·
            refine ⟨103446621173404808259155095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137928828231206411012206793 103446621173404808259155095)
            ·
              refine ⟨155169931760107212388732643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103446621173404808259155095 155169931760107212388732643)
              ·
                refine ⟨232754897640160818583098965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155169931760107212388732643 232754897640160818583098965)
                ·
                  refine ⟨2727596456720634592770691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 232754897640160818583098965 2727596456720634592770691)
                  ·
                    refine ⟨4091394685080951889156037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2727596456720634592770691 4091394685080951889156037)
                    ·
                      refine ⟨767136503452678479216757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4091394685080951889156037 767136503452678479216757)
                      ·
                        rfl

theorem cell23_1493993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 8, 1, 4].length) (baseStart_1493993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1493993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1493993 prefixEnd_1493993 := by exact prefixLift 1493993
  have htrace : WordTrace (prefixWord ++ tailWord_1493993) baseStart_1493993 baseEnd_1493993 := by
    simpa [prefixWord, tailWord_1493993, baseEnd_1493993] using wordTrace_append hprefix tailTrace_1493993
  have hstable : (prefixWord ++ tailWord_1493993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1493993).length < 2 ^ (prefixWord ++ tailWord_1493993).sum := by decide
  have hdescent : baseEnd_1493993 < baseStart_1493993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1493993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494010 : List Nat := [3, 1, 1, 1, 1, 2, 1, 3, 4, 4, 2]
def baseStart_1494010 : Nat := 118140960795 + 1494010 * 2 ^ 59
def prefixEnd_1494010 : Nat := 4983230072969 + 3 ^ 40 * 1494010 * 2
def baseEnd_1494010 : Nat := 767145232623804912704179

theorem tailTrace_1494010 : CollatzResearch.WordTrace tailWord_1494010 prefixEnd_1494010 767145232623804912704179 := by
  unfold tailWord_1494010
  simp only [CollatzResearch.WordTrace]
  refine ⟨13622755329366100359763871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36327347544976267626036989 13622755329366100359763871)
  ·
    refine ⟨20434132994049150539645807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13622755329366100359763871 20434132994049150539645807)
    ·
      refine ⟨30651199491073725809468711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20434132994049150539645807 30651199491073725809468711)
      ·
        refine ⟨45976799236610588714203067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30651199491073725809468711 45976799236610588714203067)
        ·
          refine ⟨68965198854915883071304601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45976799236610588714203067 68965198854915883071304601)
          ·
            refine ⟨51723899141186912303478451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68965198854915883071304601 51723899141186912303478451)
            ·
              refine ⟨77585848711780368455217677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51723899141186912303478451 77585848711780368455217677)
              ·
                refine ⟨29094693266917638170706629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77585848711780368455217677 29094693266917638170706629)
                ·
                  refine ⟨5455254987547057157007493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29094693266917638170706629 5455254987547057157007493)
                  ·
                    refine ⟨1022860310165073216938905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5455254987547057157007493 1022860310165073216938905)
                    ·
                      refine ⟨767145232623804912704179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1022860310165073216938905 767145232623804912704179)
                      ·
                        rfl

theorem cell23_1494010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 4, 4, 2].length) (baseStart_1494010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1494010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1494010 prefixEnd_1494010 := by exact prefixLift 1494010
  have htrace : WordTrace (prefixWord ++ tailWord_1494010) baseStart_1494010 baseEnd_1494010 := by
    simpa [prefixWord, tailWord_1494010, baseEnd_1494010] using wordTrace_append hprefix tailTrace_1494010
  have hstable : (prefixWord ++ tailWord_1494010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494010).length < 2 ^ (prefixWord ++ tailWord_1494010).sum := by decide
  have hdescent : baseEnd_1494010 < baseStart_1494010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494047 : List Nat := [1, 1, 2, 4, 1, 4, 2, 1, 2, 2, 3]
def baseStart_1494047 : Nat := 118140960795 + 1494047 * 2 ^ 59
def prefixEnd_1494047 : Nat := 4983230072969 + 3 ^ 40 * 1494047 * 2
def baseEnd_1494047 : Nat := 767164231408021267941509

theorem tailTrace_1494047 : CollatzResearch.WordTrace tailWord_1494047 prefixEnd_1494047 767164231408021267941509 := by
  unfold tailWord_1494047
  simp only [CollatzResearch.WordTrace]
  refine ⟨54492370818330356758152395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36328247212220237838768263 54492370818330356758152395)
  ·
    refine ⟨81738556227495535137228593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54492370818330356758152395 81738556227495535137228593)
    ·
      refine ⟨61303917170621651352921445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81738556227495535137228593 61303917170621651352921445)
      ·
        refine ⟨11494484469491559628672771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61303917170621651352921445 11494484469491559628672771)
        ·
          refine ⟨17241726704237339443009157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11494484469491559628672771 17241726704237339443009157)
          ·
            refine ⟨3232823757044501145564217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17241726704237339443009157 3232823757044501145564217)
            ·
              refine ⟨2424617817783375859173163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3232823757044501145564217 2424617817783375859173163)
              ·
                refine ⟨3636926726675063788759745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2424617817783375859173163 3636926726675063788759745)
                ·
                  refine ⟨2727695045006297841569809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3636926726675063788759745 2727695045006297841569809)
                  ·
                    refine ⟨2045771283754723381177357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2727695045006297841569809 2045771283754723381177357)
                    ·
                      refine ⟨767164231408021267941509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2045771283754723381177357 767164231408021267941509)
                      ·
                        rfl

theorem cell23_1494047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 1, 2, 2, 3].length) (baseStart_1494047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1494047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1494047 prefixEnd_1494047 := by exact prefixLift 1494047
  have htrace : WordTrace (prefixWord ++ tailWord_1494047) baseStart_1494047 baseEnd_1494047 := by
    simpa [prefixWord, tailWord_1494047, baseEnd_1494047] using wordTrace_append hprefix tailTrace_1494047
  have hstable : (prefixWord ++ tailWord_1494047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494047).length < 2 ^ (prefixWord ++ tailWord_1494047).sum := by decide
  have hdescent : baseEnd_1494047 < baseStart_1494047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494114 : List Nat := [3, 3, 2, 2, 1, 2, 1, 3, 1, 5]
def baseStart_1494114 : Nat := 118140960795 + 1494114 * 2 ^ 59
def prefixEnd_1494114 : Nat := 4983230072969 + 3 ^ 40 * 1494114 * 2
def baseEnd_1494114 : Nat := 255732878203957501934567

theorem tailTrace_1494114 : CollatzResearch.WordTrace tailWord_1494114 prefixEnd_1494114 255732878203957501934567 := by
  unfold tailWord_1494114
  simp only [CollatzResearch.WordTrace]
  refine ⟨13623703627271906800210349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36329876339391751467227597 13623703627271906800210349)
  ·
    refine ⟨5108888860226965050078881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13623703627271906800210349 5108888860226965050078881)
    ·
      refine ⟨3831666645170223787559161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5108888860226965050078881 3831666645170223787559161)
      ·
        refine ⟨2873749983877667840669371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3831666645170223787559161 2873749983877667840669371)
        ·
          refine ⟨4310624975816501761004057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2873749983877667840669371 4310624975816501761004057)
          ·
            refine ⟨3232968731862376320753043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4310624975816501761004057 3232968731862376320753043)
            ·
              refine ⟨4849453097793564481129565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3232968731862376320753043 4849453097793564481129565)
              ·
                refine ⟨1818544911672586680423587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4849453097793564481129565 1818544911672586680423587)
                ·
                  refine ⟨2727817367508880020635381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1818544911672586680423587 2727817367508880020635381)
                  ·
                    refine ⟨255732878203957501934567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2727817367508880020635381 255732878203957501934567)
                    ·
                      rfl

theorem cell23_1494114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_1494114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1494114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1494114 prefixEnd_1494114 := by exact prefixLift 1494114
  have htrace : WordTrace (prefixWord ++ tailWord_1494114) baseStart_1494114 baseEnd_1494114 := by
    simpa [prefixWord, tailWord_1494114, baseEnd_1494114] using wordTrace_append hprefix tailTrace_1494114
  have hstable : (prefixWord ++ tailWord_1494114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494114).length < 2 ^ (prefixWord ++ tailWord_1494114).sum := by decide
  have hdescent : baseEnd_1494114 < baseStart_1494114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494117 : List Nat := [1, 3, 1, 3, 2, 1, 3, 3, 1, 1, 4]
def baseStart_1494117 : Nat := 118140960795 + 1494117 * 2 ^ 59
def prefixEnd_1494117 : Nat := 4983230072969 + 3 ^ 40 * 1494117 * 2
def baseEnd_1494117 : Nat := 767200175053835994066187

theorem tailTrace_1494117 : CollatzResearch.WordTrace tailWord_1494117 prefixEnd_1494117 767200175053835994066187 := by
  unfold tailWord_1494117
  simp only [CollatzResearch.WordTrace]
  refine ⟨54494923928076758713200605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36329949285384505808800403 54494923928076758713200605)
  ·
    refine ⟨20435596473028784517450227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54494923928076758713200605 20435596473028784517450227)
    ·
      refine ⟨30653394709543176776175341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20435596473028784517450227 30653394709543176776175341)
      ·
        refine ⟨11495023016078691291065753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30653394709543176776175341 11495023016078691291065753)
        ·
          refine ⟨8621267262059018468299315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11495023016078691291065753 8621267262059018468299315)
          ·
            refine ⟨12931900893088527702448973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8621267262059018468299315 12931900893088527702448973)
            ·
              refine ⟨4849462834908197888418365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12931900893088527702448973 4849462834908197888418365)
              ·
                refine ⟨1818548563090574208156887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4849462834908197888418365 1818548563090574208156887)
                ·
                  refine ⟨2727822844635861312235331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1818548563090574208156887 2727822844635861312235331)
                  ·
                    refine ⟨4091734266953791968352997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2727822844635861312235331 4091734266953791968352997)
                    ·
                      refine ⟨767200175053835994066187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4091734266953791968352997 767200175053835994066187)
                      ·
                        rfl

theorem cell23_1494117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 3, 1, 1, 4].length) (baseStart_1494117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1494117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1494117 prefixEnd_1494117 := by exact prefixLift 1494117
  have htrace : WordTrace (prefixWord ++ tailWord_1494117) baseStart_1494117 baseEnd_1494117 := by
    simpa [prefixWord, tailWord_1494117, baseEnd_1494117] using wordTrace_append hprefix tailTrace_1494117
  have hstable : (prefixWord ++ tailWord_1494117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494117).length < 2 ^ (prefixWord ++ tailWord_1494117).sum := by decide
  have hdescent : baseEnd_1494117 < baseStart_1494117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494130 : List Nat := [3, 2, 1, 2, 2, 1, 2, 2, 1, 1, 6]
def baseStart_1494130 : Nat := 118140960795 + 1494130 * 2 ^ 59
def prefixEnd_1494130 : Nat := 4983230072969 + 3 ^ 40 * 1494130 * 2
def baseEnd_1494130 : Nat := 767206850302344443203627

theorem tailTrace_1494130 : CollatzResearch.WordTrace tailWord_1494130 prefixEnd_1494130 767206850302344443203627 := by
  unfold tailWord_1494130
  simp only [CollatzResearch.WordTrace]
  refine ⟨13623849519257415483355961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36330265384686441288949229 13623849519257415483355961)
  ·
    refine ⟨10217887139443061612516971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13623849519257415483355961 10217887139443061612516971)
    ·
      refine ⟨15326830709164592418775457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10217887139443061612516971 15326830709164592418775457)
      ·
        refine ⟨11495123031873444314081593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15326830709164592418775457 11495123031873444314081593)
        ·
          refine ⟨8621342273905083235561195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11495123031873444314081593 8621342273905083235561195)
          ·
            refine ⟨12932013410857624853341793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8621342273905083235561195 12932013410857624853341793)
            ·
              refine ⟨9699010058143218640006345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12932013410857624853341793 9699010058143218640006345)
              ·
                refine ⟨7274257543607413980004759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9699010058143218640006345 7274257543607413980004759)
                ·
                  refine ⟨10911386315411120970007139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7274257543607413980004759 10911386315411120970007139)
                  ·
                    refine ⟨16367079473116681455010709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10911386315411120970007139 16367079473116681455010709)
                    ·
                      refine ⟨767206850302344443203627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16367079473116681455010709 767206850302344443203627)
                      ·
                        rfl

theorem cell23_1494130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_1494130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1494130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1494130 prefixEnd_1494130 := by exact prefixLift 1494130
  have htrace : WordTrace (prefixWord ++ tailWord_1494130) baseStart_1494130 baseEnd_1494130 := by
    simpa [prefixWord, tailWord_1494130, baseEnd_1494130] using wordTrace_append hprefix tailTrace_1494130
  have hstable : (prefixWord ++ tailWord_1494130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494130).length < 2 ^ (prefixWord ++ tailWord_1494130).sum := by decide
  have hdescent : baseEnd_1494130 < baseStart_1494130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494137 : List Nat := [1, 2, 1, 3, 5, 1, 1, 2, 1, 1, 5]
def baseStart_1494137 : Nat := 118140960795 + 1494137 * 2 ^ 59
def prefixEnd_1494137 : Nat := 4983230072969 + 3 ^ 40 * 1494137 * 2
def baseEnd_1494137 : Nat := 767210444666925915816095

theorem tailTrace_1494137 : CollatzResearch.WordTrace tailWord_1494137 prefixEnd_1494137 767210444666925915816095 := by
  unfold tailWord_1494137
  simp only [CollatzResearch.WordTrace]
  refine ⟨54495653388004302128928665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36330435592002868085952443 54495653388004302128928665)
  ·
    refine ⟨40871740041003226596696499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54495653388004302128928665 40871740041003226596696499)
    ·
      refine ⟨61307610061504839895044749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40871740041003226596696499 61307610061504839895044749)
      ·
        refine ⟨22990353773064314960641781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61307610061504839895044749 22990353773064314960641781)
        ·
          refine ⟨2155345666224779527560167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22990353773064314960641781 2155345666224779527560167)
          ·
            refine ⟨3233018499337169291340251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2155345666224779527560167 3233018499337169291340251)
            ·
              refine ⟨4849527749005753937010377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3233018499337169291340251 4849527749005753937010377)
              ·
                refine ⟨3637145811754315452757783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4849527749005753937010377 3637145811754315452757783)
                ·
                  refine ⟨5455718717631473179136675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3637145811754315452757783 5455718717631473179136675)
                  ·
                    refine ⟨8183578076447209768705013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5455718717631473179136675 8183578076447209768705013)
                    ·
                      refine ⟨767210444666925915816095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8183578076447209768705013 767210444666925915816095)
                      ·
                        rfl

theorem cell23_1494137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 2, 1, 1, 5].length) (baseStart_1494137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1494137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1494137 prefixEnd_1494137 := by exact prefixLift 1494137
  have htrace : WordTrace (prefixWord ++ tailWord_1494137) baseStart_1494137 baseEnd_1494137 := by
    simpa [prefixWord, tailWord_1494137, baseEnd_1494137] using wordTrace_append hprefix tailTrace_1494137
  have hstable : (prefixWord ++ tailWord_1494137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494137).length < 2 ^ (prefixWord ++ tailWord_1494137).sum := by decide
  have hdescent : baseEnd_1494137 < baseStart_1494137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494154 : List Nat := [3, 1, 2, 3, 1, 1, 4, 2, 1, 2, 3]
def baseStart_1494154 : Nat := 118140960795 + 1494154 * 2 ^ 59
def prefixEnd_1494154 : Nat := 4983230072969 + 3 ^ 40 * 1494154 * 2
def baseEnd_1494154 : Nat := 767219173838052349303517

theorem tailTrace_1494154 : CollatzResearch.WordTrace tailWord_1494154 prefixEnd_1494154 767219173838052349303517 := by
  unfold tailWord_1494154
  simp only [CollatzResearch.WordTrace]
  refine ⟨13624068357235678508074379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36330848952628476021531677 13624068357235678508074379)
  ·
    refine ⟨20436102535853517762111569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13624068357235678508074379 20436102535853517762111569)
    ·
      refine ⟨15327076901890138321583677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20436102535853517762111569 15327076901890138321583677)
      ·
        refine ⟨5747653838208801870593879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15327076901890138321583677 5747653838208801870593879)
        ·
          refine ⟨8621480757313202805890819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5747653838208801870593879 8621480757313202805890819)
          ·
            refine ⟨12932221135969804208836229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8621480757313202805890819 12932221135969804208836229)
            ·
              refine ⟨2424791462994338289156793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12932221135969804208836229 2424791462994338289156793)
              ·
                refine ⟨1818593597245753716867595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2424791462994338289156793 1818593597245753716867595)
                ·
                  refine ⟨2727890395868630575301393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1818593597245753716867595 2727890395868630575301393)
                  ·
                    refine ⟨2045917796901472931476045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2727890395868630575301393 2045917796901472931476045)
                    ·
                      refine ⟨767219173838052349303517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2045917796901472931476045 767219173838052349303517)
                      ·
                        rfl

theorem cell23_1494154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_1494154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1494154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1494154 prefixEnd_1494154 := by exact prefixLift 1494154
  have htrace : WordTrace (prefixWord ++ tailWord_1494154) baseStart_1494154 baseEnd_1494154 := by
    simpa [prefixWord, tailWord_1494154, baseEnd_1494154] using wordTrace_append hprefix tailTrace_1494154
  have hstable : (prefixWord ++ tailWord_1494154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494154).length < 2 ^ (prefixWord ++ tailWord_1494154).sum := by decide
  have hdescent : baseEnd_1494154 < baseStart_1494154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494168 : List Nat := [2, 1, 2, 4, 2, 1, 3, 3, 1, 2, 2]
def baseStart_1494168 : Nat := 118140960795 + 1494168 * 2 ^ 59
def prefixEnd_1494168 : Nat := 4983230072969 + 3 ^ 40 * 1494168 * 2
def baseEnd_1494168 : Nat := 767226362567215294528453

theorem tailTrace_1494168 : CollatzResearch.WordTrace tailWord_1494168 prefixEnd_1494168 767226362567215294528453 := by
  unfold tailWord_1494168
  simp only [CollatzResearch.WordTrace]
  refine ⟨27248392025445997211653579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36331189367261329615538105 27248392025445997211653579)
  ·
    refine ⟨40872588038168995817480369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27248392025445997211653579 40872588038168995817480369)
    ·
      refine ⟨30654441028626746863110277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40872588038168995817480369 30654441028626746863110277)
      ·
        refine ⟨5747707692867515036833177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30654441028626746863110277 5747707692867515036833177)
        ·
          refine ⟨4310780769650636277624883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5747707692867515036833177 4310780769650636277624883)
          ·
            refine ⟨6466171154475954416437325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4310780769650636277624883 6466171154475954416437325)
            ·
              refine ⟨2424814182928482906163997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6466171154475954416437325 2424814182928482906163997)
              ·
                refine ⟨909305318598181089811499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2424814182928482906163997 909305318598181089811499)
                ·
                  refine ⟨1363957977897271634717249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 909305318598181089811499 1363957977897271634717249)
                  ·
                    refine ⟨1022968483422953726037937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1363957977897271634717249 1022968483422953726037937)
                    ·
                      refine ⟨767226362567215294528453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1022968483422953726037937 767226362567215294528453)
                      ·
                        rfl

theorem cell23_1494168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 3, 1, 2, 2].length) (baseStart_1494168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1494168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1494168 prefixEnd_1494168 := by exact prefixLift 1494168
  have htrace : WordTrace (prefixWord ++ tailWord_1494168) baseStart_1494168 baseEnd_1494168 := by
    simpa [prefixWord, tailWord_1494168, baseEnd_1494168] using wordTrace_append hprefix tailTrace_1494168
  have hstable : (prefixWord ++ tailWord_1494168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494168).length < 2 ^ (prefixWord ++ tailWord_1494168).sum := by decide
  have hdescent : baseEnd_1494168 < baseStart_1494168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494201 : List Nat := [1, 2, 1, 4, 1, 3, 4, 1, 2, 1, 3]
def baseStart_1494201 : Nat := 118140960795 + 1494201 * 2 ^ 59
def prefixEnd_1494201 : Nat := 4983230072969 + 3 ^ 40 * 1494201 * 2
def baseEnd_1494201 : Nat := 767243307428813665415801

theorem tailTrace_1494201 : CollatzResearch.WordTrace tailWord_1494201 prefixEnd_1494201 767243307428813665415801 := by
  unfold tailWord_1494201
  simp only [CollatzResearch.WordTrace]
  refine ⟨54497987659772441059258457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36331991773181627372838971 54497987659772441059258457)
  ·
    refine ⟨40873490744829330794443843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54497987659772441059258457 40873490744829330794443843)
    ·
      refine ⟨61310236117243996191665765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40873490744829330794443843 61310236117243996191665765)
      ·
        refine ⟨11495669271983249285937331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61310236117243996191665765 11495669271983249285937331)
        ·
          refine ⟨17243503907974873928905997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11495669271983249285937331 17243503907974873928905997)
          ·
            refine ⟨6466313965490577723339749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17243503907974873928905997 6466313965490577723339749)
            ·
              refine ⟨1212433868529483323126203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6466313965490577723339749 1212433868529483323126203)
              ·
                refine ⟨1818650802794224984689305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1212433868529483323126203 1818650802794224984689305)
                ·
                  refine ⟨1363988102095668738516979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1818650802794224984689305 1363988102095668738516979)
                  ·
                    refine ⟨2045982153143503107775469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1363988102095668738516979 2045982153143503107775469)
                    ·
                      refine ⟨767243307428813665415801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2045982153143503107775469 767243307428813665415801)
                      ·
                        rfl

theorem cell23_1494201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 4, 1, 2, 1, 3].length) (baseStart_1494201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1494201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1494201 prefixEnd_1494201 := by exact prefixLift 1494201
  have htrace : WordTrace (prefixWord ++ tailWord_1494201) baseStart_1494201 baseEnd_1494201 := by
    simpa [prefixWord, tailWord_1494201, baseEnd_1494201] using wordTrace_append hprefix tailTrace_1494201
  have hstable : (prefixWord ++ tailWord_1494201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494201).length < 2 ^ (prefixWord ++ tailWord_1494201).sum := by decide
  have hdescent : baseEnd_1494201 < baseStart_1494201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494241 : List Nat := [1, 2, 3, 1, 3, 2, 1, 4, 2, 2, 2]
def baseStart_1494241 : Nat := 118140960795 + 1494241 * 2 ^ 59
def prefixEnd_1494241 : Nat := 4983230072969 + 3 ^ 40 * 1494241 * 2
def baseEnd_1494241 : Nat := 767263846654993508915617

theorem tailTrace_1494241 : CollatzResearch.WordTrace tailWord_1494241 prefixEnd_1494241 767263846654993508915617 := by
  unfold tailWord_1494241
  simp only [CollatzResearch.WordTrace]
  refine ⟨54499446579627527890714577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36332964386418351927143051 54499446579627527890714577)
  ·
    refine ⟨40874584934720645918035933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54499446579627527890714577 40874584934720645918035933)
    ·
      refine ⟨15327969350520242219263475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40874584934720645918035933 15327969350520242219263475)
      ·
        refine ⟨22991954025780363328895213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15327969350520242219263475 22991954025780363328895213)
        ·
          refine ⟨8621982759667636248335705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22991954025780363328895213 8621982759667636248335705)
          ·
            refine ⟨6466487069750727186251779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8621982759667636248335705 6466487069750727186251779)
            ·
              refine ⟨9699730604626090779377669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6466487069750727186251779 9699730604626090779377669)
              ·
                refine ⟨1818699488367392021133313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9699730604626090779377669 1818699488367392021133313)
                ·
                  refine ⟨1364024616275544015849985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1818699488367392021133313 1364024616275544015849985)
                  ·
                    refine ⟨1023018462206658011887489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1364024616275544015849985 1023018462206658011887489)
                    ·
                      refine ⟨767263846654993508915617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1023018462206658011887489 767263846654993508915617)
                      ·
                        rfl

theorem cell23_1494241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 4, 2, 2, 2].length) (baseStart_1494241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1494241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1494241 prefixEnd_1494241 := by exact prefixLift 1494241
  have htrace : WordTrace (prefixWord ++ tailWord_1494241) baseStart_1494241 baseEnd_1494241 := by
    simpa [prefixWord, tailWord_1494241, baseEnd_1494241] using wordTrace_append hprefix tailTrace_1494241
  have hstable : (prefixWord ++ tailWord_1494241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494241).length < 2 ^ (prefixWord ++ tailWord_1494241).sum := by decide
  have hdescent : baseEnd_1494241 < baseStart_1494241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494314 : List Nat := [3, 1, 4, 2, 1, 1, 1, 2, 1, 3, 4]
def baseStart_1494314 : Nat := 118140960795 + 1494314 * 2 ^ 59
def prefixEnd_1494314 : Nat := 4983230072969 + 3 ^ 40 * 1494314 * 2
def baseEnd_1494314 : Nat := 767301330742771723302781

theorem tailTrace_1494314 : CollatzResearch.WordTrace tailWord_1494314 prefixEnd_1494314 767301330742771723302781 := by
  unfold tailWord_1494314
  simp only [CollatzResearch.WordTrace]
  refine ⟨13625527277090765339530499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36334739405575374238747997 13625527277090765339530499)
  ·
    refine ⟨20438290915636148009295749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13625527277090765339530499 20438290915636148009295749)
    ·
      refine ⟨3832179546681777751742953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20438290915636148009295749 3832179546681777751742953)
      ·
        refine ⟨2874134660011333313807215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3832179546681777751742953 2874134660011333313807215)
        ·
          refine ⟨4311201990016999970710823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2874134660011333313807215 4311201990016999970710823)
          ·
            refine ⟨6466802985025499956066235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4311201990016999970710823 6466802985025499956066235)
            ·
              refine ⟨9700204477538249934099353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6466802985025499956066235 9700204477538249934099353)
              ·
                refine ⟨7275153358153687450574515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9700204477538249934099353 7275153358153687450574515)
                ·
                  refine ⟨10912730037230531175861773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7275153358153687450574515 10912730037230531175861773)
                  ·
                    refine ⟨4092273763961449190948165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10912730037230531175861773 4092273763961449190948165)
                    ·
                      refine ⟨767301330742771723302781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4092273763961449190948165 767301330742771723302781)
                      ·
                        rfl

theorem cell23_1494314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_1494314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1494314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1494314 prefixEnd_1494314 := by exact prefixLift 1494314
  have htrace : WordTrace (prefixWord ++ tailWord_1494314) baseStart_1494314 baseEnd_1494314 := by
    simpa [prefixWord, tailWord_1494314, baseEnd_1494314] using wordTrace_append hprefix tailTrace_1494314
  have hstable : (prefixWord ++ tailWord_1494314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494314).length < 2 ^ (prefixWord ++ tailWord_1494314).sum := by decide
  have hdescent : baseEnd_1494314 < baseStart_1494314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494334 : List Nat := [4, 2, 1, 2, 1, 1, 1, 3, 1, 4, 3]
def baseStart_1494334 : Nat := 118140960795 + 1494334 * 2 ^ 59
def prefixEnd_1494334 : Nat := 4983230072969 + 3 ^ 40 * 1494334 * 2
def baseEnd_1494334 : Nat := 767311600355861645052689

theorem tailTrace_1494334 : CollatzResearch.WordTrace tailWord_1494334 prefixEnd_1494334 767311600355861645052689 := by
  unfold tailWord_1494334
  simp only [CollatzResearch.WordTrace]
  refine ⟨6812854821036325596731257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36335225712193736515900037 6812854821036325596731257)
  ·
    refine ⟨5109641115777244197548443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6812854821036325596731257 5109641115777244197548443)
    ·
      refine ⟨7664461673665866296322665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5109641115777244197548443 7664461673665866296322665)
      ·
        refine ⟨5748346255249399722241999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7664461673665866296322665 5748346255249399722241999)
        ·
          refine ⟨8622519382874099583362999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5748346255249399722241999 8622519382874099583362999)
          ·
            refine ⟨12933779074311149375044499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8622519382874099583362999 12933779074311149375044499)
            ·
              refine ⟨19400668611466724062566749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12933779074311149375044499 19400668611466724062566749)
              ·
                refine ⟨7275250729300021523462531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19400668611466724062566749 7275250729300021523462531)
                ·
                  refine ⟨10912876093950032285193797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7275250729300021523462531 10912876093950032285193797)
                  ·
                    refine ⟨2046164267615631053473837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10912876093950032285193797 2046164267615631053473837)
                    ·
                      refine ⟨767311600355861645052689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2046164267615631053473837 767311600355861645052689)
                      ·
                        rfl

theorem cell23_1494334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_1494334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1494334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1494334 prefixEnd_1494334 := by exact prefixLift 1494334
  have htrace : WordTrace (prefixWord ++ tailWord_1494334) baseStart_1494334 baseEnd_1494334 := by
    simpa [prefixWord, tailWord_1494334, baseEnd_1494334] using wordTrace_append hprefix tailTrace_1494334
  have hstable : (prefixWord ++ tailWord_1494334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494334).length < 2 ^ (prefixWord ++ tailWord_1494334).sum := by decide
  have hdescent : baseEnd_1494334 < baseStart_1494334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494367 : List Nat := [1, 1, 2, 3, 1, 2, 1, 4, 3, 5]
def baseStart_1494367 : Nat := 118140960795 + 1494367 * 2 ^ 59
def prefixEnd_1494367 : Nat := 4983230072969 + 3 ^ 40 * 1494367 * 2
def baseEnd_1494367 : Nat := 255776181739153338646679

theorem tailTrace_1494367 : CollatzResearch.WordTrace tailWord_1494367 prefixEnd_1494367 255776181739153338646679 := by
  unfold tailWord_1494367
  simp only [CollatzResearch.WordTrace]
  refine ⟨54504042177171051409801355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36336028118114034273200903 54504042177171051409801355)
  ·
    refine ⟨81756063265756577114702033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54504042177171051409801355 81756063265756577114702033)
    ·
      refine ⟨61317047449317432836026525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81756063265756577114702033 61317047449317432836026525)
      ·
        refine ⟨22993892793494037313509947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61317047449317432836026525 22993892793494037313509947)
        ·
          refine ⟨34490839190241055970264921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22993892793494037313509947 34490839190241055970264921)
          ·
            refine ⟨25868129392680791977698691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34490839190241055970264921 25868129392680791977698691)
            ·
              refine ⟨38802194089021187966548037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25868129392680791977698691 38802194089021187966548037)
              ·
                refine ⟨7275411391691472743727757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38802194089021187966548037 7275411391691472743727757)
                ·
                  refine ⟨2728279271884302278897909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7275411391691472743727757 2728279271884302278897909)
                  ·
                    refine ⟨255776181739153338646679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2728279271884302278897909 255776181739153338646679)
                    ·
                      rfl

theorem cell23_1494367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 3, 5].length) (baseStart_1494367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1494367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1494367 prefixEnd_1494367 := by exact prefixLift 1494367
  have htrace : WordTrace (prefixWord ++ tailWord_1494367) baseStart_1494367 baseEnd_1494367 := by
    simpa [prefixWord, tailWord_1494367, baseEnd_1494367] using wordTrace_append hprefix tailTrace_1494367
  have hstable : (prefixWord ++ tailWord_1494367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494367).length < 2 ^ (prefixWord ++ tailWord_1494367).sum := by decide
  have hdescent : baseEnd_1494367 < baseStart_1494367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494371 : List Nat := [1, 1, 1, 5, 2, 4, 2, 1, 6]
def baseStart_1494371 : Nat := 118140960795 + 1494371 * 2 ^ 59
def prefixEnd_1494371 : Nat := 4983230072969 + 3 ^ 40 * 1494371 * 2
def baseEnd_1494371 : Nat := 85258955460008666698891

theorem tailTrace_1494371 : CollatzResearch.WordTrace tailWord_1494371 prefixEnd_1494371 85258955460008666698891 := by
  unfold tailWord_1494371
  simp only [CollatzResearch.WordTrace]
  refine ⟨54504188069156560092946967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36336125379437706728631311 54504188069156560092946967)
  ·
    refine ⟨81756282103734840139420451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54504188069156560092946967 81756282103734840139420451)
    ·
      refine ⟨122634423155602260209130677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81756282103734840139420451 122634423155602260209130677)
      ·
        refine ⟨11496977170837711894606001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 122634423155602260209130677 11496977170837711894606001)
        ·
          refine ⟨8622732878128283920954501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11496977170837711894606001 8622732878128283920954501)
          ·
            refine ⟨1616762414649053235178969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8622732878128283920954501 1616762414649053235178969)
            ·
              refine ⟨1212571810986789926384227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1616762414649053235178969 1212571810986789926384227)
              ·
                refine ⟨1818857716480184889576341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1212571810986789926384227 1818857716480184889576341)
                ·
                  refine ⟨85258955460008666698891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1818857716480184889576341 85258955460008666698891)
                  ·
                    rfl

theorem cell23_1494371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 2, 1, 6].length) (baseStart_1494371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1494371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1494371 prefixEnd_1494371 := by exact prefixLift 1494371
  have htrace : WordTrace (prefixWord ++ tailWord_1494371) baseStart_1494371 baseEnd_1494371 := by
    simpa [prefixWord, tailWord_1494371, baseEnd_1494371] using wordTrace_append hprefix tailTrace_1494371
  have hstable : (prefixWord ++ tailWord_1494371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494371).length < 2 ^ (prefixWord ++ tailWord_1494371).sum := by decide
  have hdescent : baseEnd_1494371 < baseStart_1494371 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494391 : List Nat := [1, 1, 3, 1, 1, 2, 6, 1, 2, 3, 2]
def baseStart_1494391 : Nat := 118140960795 + 1494391 * 2 ^ 59
def prefixEnd_1494391 : Nat := 4983230072969 + 3 ^ 40 * 1494391 * 2
def baseEnd_1494391 : Nat := 767340868753167922039927

theorem tailTrace_1494391 : CollatzResearch.WordTrace tailWord_1494391 prefixEnd_1494391 767340868753167922039927 := by
  unfold tailWord_1494391
  simp only [CollatzResearch.WordTrace]
  refine ⟨54504917529084103508675027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36336611686056069005783351 54504917529084103508675027)
  ·
    refine ⟨81757376293626155263012541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54504917529084103508675027 81757376293626155263012541)
    ·
      refine ⟨30659016110109808223629703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81757376293626155263012541 30659016110109808223629703)
      ·
        refine ⟨45988524165164712335444555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30659016110109808223629703 45988524165164712335444555)
        ·
          refine ⟨68982786247747068503166833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45988524165164712335444555 68982786247747068503166833)
          ·
            refine ⟨51737089685810301377375125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68982786247747068503166833 51737089685810301377375125)
            ·
              refine ⟨2425176079022357877064459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 51737089685810301377375125 2425176079022357877064459)
              ·
                refine ⟨3637764118533536815596689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2425176079022357877064459 3637764118533536815596689)
                ·
                  refine ⟨2728323088900152611697517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3637764118533536815596689 2728323088900152611697517)
                  ·
                    refine ⟨1023121158337557229386569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2728323088900152611697517 1023121158337557229386569)
                    ·
                      refine ⟨767340868753167922039927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1023121158337557229386569 767340868753167922039927)
                      ·
                        rfl

theorem cell23_1494391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 1, 2, 3, 2].length) (baseStart_1494391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1494391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1494391 prefixEnd_1494391 := by exact prefixLift 1494391
  have htrace : WordTrace (prefixWord ++ tailWord_1494391) baseStart_1494391 baseEnd_1494391 := by
    simpa [prefixWord, tailWord_1494391, baseEnd_1494391] using wordTrace_append hprefix tailTrace_1494391
  have hstable : (prefixWord ++ tailWord_1494391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494391).length < 2 ^ (prefixWord ++ tailWord_1494391).sum := by decide
  have hdescent : baseEnd_1494391 < baseStart_1494391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494431 : List Nat := [1, 1, 2, 5, 1, 2, 2, 3, 2, 4]
def baseStart_1494431 : Nat := 118140960795 + 1494431 * 2 ^ 59
def prefixEnd_1494431 : Nat := 4983230072969 + 3 ^ 40 * 1494431 * 2
def baseEnd_1494431 : Nat := 255787135993115921846581

theorem tailTrace_1494431 : CollatzResearch.WordTrace tailWord_1494431 prefixEnd_1494431 255787135993115921846581 := by
  unfold tailWord_1494431
  simp only [CollatzResearch.WordTrace]
  refine ⟨54506376448939190340131147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36337584299292793560087431 54506376448939190340131147)
  ·
    refine ⟨81759564673408785510196721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54506376448939190340131147 81759564673408785510196721)
    ·
      refine ⟨61319673505056589132647541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81759564673408785510196721 61319673505056589132647541)
      ·
        refine ⟨5748719391099055231185707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61319673505056589132647541 5748719391099055231185707)
        ·
          refine ⟨8623079086648582846778561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5748719391099055231185707 8623079086648582846778561)
          ·
            refine ⟨6467309314986437135083921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8623079086648582846778561 6467309314986437135083921)
            ·
              refine ⟨4850481986239827851312941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6467309314986437135083921 4850481986239827851312941)
              ·
                refine ⟨1818930744839935444242353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4850481986239827851312941 1818930744839935444242353)
                ·
                  refine ⟨1364198058629951583181765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1818930744839935444242353 1364198058629951583181765)
                  ·
                    refine ⟨255787135993115921846581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1364198058629951583181765 255787135993115921846581)
                    ·
                      rfl

theorem cell23_1494431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 3, 2, 4].length) (baseStart_1494431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1494431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1494431 prefixEnd_1494431 := by exact prefixLift 1494431
  have htrace : WordTrace (prefixWord ++ tailWord_1494431) baseStart_1494431 baseEnd_1494431 := by
    simpa [prefixWord, tailWord_1494431, baseEnd_1494431] using wordTrace_append hprefix tailTrace_1494431
  have hstable : (prefixWord ++ tailWord_1494431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494431).length < 2 ^ (prefixWord ++ tailWord_1494431).sum := by decide
  have hdescent : baseEnd_1494431 < baseStart_1494431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494455 : List Nat := [1, 1, 3, 1, 3, 2, 4, 3, 1, 2, 2]
def baseStart_1494455 : Nat := 118140960795 + 1494455 * 2 ^ 59
def prefixEnd_1494455 : Nat := 4983230072969 + 3 ^ 40 * 1494455 * 2
def baseEnd_1494455 : Nat := 767373731515055671639633

theorem tailTrace_1494455 : CollatzResearch.WordTrace tailWord_1494455 prefixEnd_1494455 767373731515055671639633 := by
  unfold tailWord_1494455
  simp only [CollatzResearch.WordTrace]
  refine ⟨54507251800852242439004819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36338167867234828292669879 54507251800852242439004819)
  ·
    refine ⟨81760877701278363658507229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54507251800852242439004819 81760877701278363658507229)
    ·
      refine ⟨30660329137979386371940211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81760877701278363658507229 30660329137979386371940211)
      ·
        refine ⟨45990493706969079557910317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30660329137979386371940211 45990493706969079557910317)
        ·
          refine ⟨17246435140113404834216369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45990493706969079557910317 17246435140113404834216369)
          ·
            refine ⟨12934826355085053625662277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17246435140113404834216369 12934826355085053625662277)
            ·
              refine ⟨2425279941578447554811677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12934826355085053625662277 2425279941578447554811677)
              ·
                refine ⟨909479978091917833054379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2425279941578447554811677 909479978091917833054379)
                ·
                  refine ⟨1364219967137876749581569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 909479978091917833054379 1364219967137876749581569)
                  ·
                    refine ⟨1023164975353407562186177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1364219967137876749581569 1023164975353407562186177)
                    ·
                      refine ⟨767373731515055671639633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1023164975353407562186177 767373731515055671639633)
                      ·
                        rfl

theorem cell23_1494455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 3, 1, 2, 2].length) (baseStart_1494455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1494455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1494455 prefixEnd_1494455 := by exact prefixLift 1494455
  have htrace : WordTrace (prefixWord ++ tailWord_1494455) baseStart_1494455 baseEnd_1494455 := by
    simpa [prefixWord, tailWord_1494455, baseEnd_1494455] using wordTrace_append hprefix tailTrace_1494455
  have hstable : (prefixWord ++ tailWord_1494455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494455).length < 2 ^ (prefixWord ++ tailWord_1494455).sum := by decide
  have hdescent : baseEnd_1494455 < baseStart_1494455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494471 : List Nat := [1, 1, 4, 1, 1, 3, 3, 1, 4, 1, 3]
def baseStart_1494471 : Nat := 118140960795 + 1494471 * 2 ^ 59
def prefixEnd_1494471 : Nat := 4983230072969 + 3 ^ 40 * 1494471 * 2
def baseEnd_1494471 : Nat := 767381947205527609039559

theorem tailTrace_1494471 : CollatzResearch.WordTrace tailWord_1494471 prefixEnd_1494471 767381947205527609039559 := by
  unfold tailWord_1494471
  simp only [CollatzResearch.WordTrace]
  refine ⟨54507835368794277171587267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36338556912529518114391511 54507835368794277171587267)
  ·
    refine ⟨81761753053191415757380901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54507835368794277171587267 81761753053191415757380901)
    ·
      refine ⟨15330328697473390454508919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81761753053191415757380901 15330328697473390454508919)
      ·
        refine ⟨22995493046210085681763379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15330328697473390454508919 22995493046210085681763379)
        ·
          refine ⟨34493239569315128522645069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22995493046210085681763379 34493239569315128522645069)
          ·
            refine ⟨12934964838493173195991901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34493239569315128522645069 12934964838493173195991901)
            ·
              refine ⟨4850611814434939948496963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12934964838493173195991901 4850611814434939948496963)
              ·
                refine ⟨7275917721652409922745445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4850611814434939948496963 7275917721652409922745445)
                ·
                  refine ⟨1364234572809826860514771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7275917721652409922745445 1364234572809826860514771)
                  ·
                    refine ⟨2046351859214740290772157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1364234572809826860514771 2046351859214740290772157)
                    ·
                      refine ⟨767381947205527609039559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2046351859214740290772157 767381947205527609039559)
                      ·
                        rfl

theorem cell23_1494471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 4, 1, 3].length) (baseStart_1494471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1494471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1494471 prefixEnd_1494471 := by exact prefixLift 1494471
  have htrace : WordTrace (prefixWord ++ tailWord_1494471) baseStart_1494471 baseEnd_1494471 := by
    simpa [prefixWord, tailWord_1494471, baseEnd_1494471] using wordTrace_append hprefix tailTrace_1494471
  have hstable : (prefixWord ++ tailWord_1494471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494471).length < 2 ^ (prefixWord ++ tailWord_1494471).sum := by decide
  have hdescent : baseEnd_1494471 < baseStart_1494471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494511 : List Nat := [1, 1, 2, 1, 4, 1, 2, 4, 1, 4, 2]
def baseStart_1494511 : Nat := 118140960795 + 1494511 * 2 ^ 59
def prefixEnd_1494511 : Nat := 4983230072969 + 3 ^ 40 * 1494511 * 2
def baseEnd_1494511 : Nat := 767402486431707452539375

theorem tailTrace_1494511 : CollatzResearch.WordTrace tailWord_1494511 prefixEnd_1494511 767402486431707452539375 := by
  unfold tailWord_1494511
  simp only [CollatzResearch.WordTrace]
  refine ⟨54509294288649364003043387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36339529525766242668695591 54509294288649364003043387)
  ·
    refine ⟨81763941432974046004565081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54509294288649364003043387 81763941432974046004565081)
    ·
      refine ⟨61322956074730534503423811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81763941432974046004565081 61322956074730534503423811)
      ·
        refine ⟨91984434112095801755135717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61322956074730534503423811 91984434112095801755135717)
        ·
          refine ⟨17247081396017962829087947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91984434112095801755135717 17247081396017962829087947)
          ·
            refine ⟨25870622094026944243631921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17247081396017962829087947 25870622094026944243631921)
            ·
              refine ⟨19402966570520208182723941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25870622094026944243631921 19402966570520208182723941)
              ·
                refine ⟨3638056231972539034260739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19402966570520208182723941 3638056231972539034260739)
                ·
                  refine ⟨5457084347958808551391109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3638056231972539034260739 5457084347958808551391109)
                  ·
                    refine ⟨1023203315242276603385833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5457084347958808551391109 1023203315242276603385833)
                    ·
                      refine ⟨767402486431707452539375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1023203315242276603385833 767402486431707452539375)
                      ·
                        rfl

theorem cell23_1494511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 4, 1, 4, 2].length) (baseStart_1494511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1494511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1494511 prefixEnd_1494511 := by exact prefixLift 1494511
  have htrace : WordTrace (prefixWord ++ tailWord_1494511) baseStart_1494511 baseEnd_1494511 := by
    simpa [prefixWord, tailWord_1494511, baseEnd_1494511] using wordTrace_append hprefix tailTrace_1494511
  have hstable : (prefixWord ++ tailWord_1494511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494511).length < 2 ^ (prefixWord ++ tailWord_1494511).sum := by decide
  have hdescent : baseEnd_1494511 < baseStart_1494511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494524 : List Nat := [2, 2, 2, 1, 2, 1, 2, 1, 4, 2, 4]
def baseStart_1494524 : Nat := 118140960795 + 1494524 * 2 ^ 59
def prefixEnd_1494524 : Nat := 4983230072969 + 3 ^ 40 * 1494524 * 2
def baseEnd_1494524 : Nat := 767409161680215901676815

theorem tailTrace_1494524 : CollatzResearch.WordTrace tailWord_1494524 prefixEnd_1494524 767409161680215901676815 := by
  unfold tailWord_1494524
  simp only [CollatzResearch.WordTrace]
  refine ⟨27254884218801133611633313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36339845625068178148844417 27254884218801133611633313)
  ·
    refine ⟨20441163164100850208724985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27254884218801133611633313 20441163164100850208724985)
    ·
      refine ⟨15330872373075637656543739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20441163164100850208724985 15330872373075637656543739)
      ·
        refine ⟨22996308559613456484815609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15330872373075637656543739 22996308559613456484815609)
        ·
          refine ⟨17247231419710092363611707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22996308559613456484815609 17247231419710092363611707)
          ·
            refine ⟨25870847129565138545417561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17247231419710092363611707 25870847129565138545417561)
            ·
              refine ⟨19403135347173853909063171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25870847129565138545417561 19403135347173853909063171)
              ·
                refine ⟨29104703020760780863594757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19403135347173853909063171 29104703020760780863594757)
                ·
                  refine ⟨5457131816392646411924017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29104703020760780863594757 5457131816392646411924017)
                  ·
                    refine ⟨4092848862294484808943013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5457131816392646411924017 4092848862294484808943013)
                    ·
                      refine ⟨767409161680215901676815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4092848862294484808943013 767409161680215901676815)
                      ·
                        rfl

theorem cell23_1494524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 4, 2, 4].length) (baseStart_1494524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1494524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1494524 prefixEnd_1494524 := by exact prefixLift 1494524
  have htrace : WordTrace (prefixWord ++ tailWord_1494524) baseStart_1494524 baseEnd_1494524 := by
    simpa [prefixWord, tailWord_1494524, baseEnd_1494524] using wordTrace_append hprefix tailTrace_1494524
  have hstable : (prefixWord ++ tailWord_1494524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494524).length < 2 ^ (prefixWord ++ tailWord_1494524).sum := by decide
  have hdescent : baseEnd_1494524 < baseStart_1494524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494581 : List Nat := [1, 3, 3, 1, 1, 3, 2, 2, 2, 5]
def baseStart_1494581 : Nat := 118140960795 + 1494581 * 2 ^ 59
def prefixEnd_1494581 : Nat := 4983230072969 + 3 ^ 40 * 1494581 * 2
def baseEnd_1494581 : Nat := 255812810025840726221351

theorem tailTrace_1494581 : CollatzResearch.WordTrace tailWord_1494581 prefixEnd_1494581 255812810025840726221351 := by
  unfold tailWord_1494581
  simp only [CollatzResearch.WordTrace]
  refine ⟨54511847398395765958091597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36341231598930510638727731 54511847398395765958091597)
  ·
    refine ⟨20441942774398412234284349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54511847398395765958091597 20441942774398412234284349)
    ·
      refine ⟨7665728540399404587856631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20441942774398412234284349 7665728540399404587856631)
      ·
        refine ⟨11498592810599106881784947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7665728540399404587856631 11498592810599106881784947)
        ·
          refine ⟨17247889215898660322677421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11498592810599106881784947 17247889215898660322677421)
          ·
            refine ⟨6467958455961997621004033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17247889215898660322677421 6467958455961997621004033)
            ·
              refine ⟨4850968841971498215753025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6467958455961997621004033 4850968841971498215753025)
              ·
                refine ⟨3638226631478623661814769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4850968841971498215753025 3638226631478623661814769)
                ·
                  refine ⟨2728669973608967746361077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3638226631478623661814769 2728669973608967746361077)
                  ·
                    refine ⟨255812810025840726221351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2728669973608967746361077 255812810025840726221351)
                    ·
                      rfl

theorem cell23_1494581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_1494581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1494581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1494581 prefixEnd_1494581 := by exact prefixLift 1494581
  have htrace : WordTrace (prefixWord ++ tailWord_1494581) baseStart_1494581 baseEnd_1494581 := by
    simpa [prefixWord, tailWord_1494581, baseEnd_1494581] using wordTrace_append hprefix tailTrace_1494581
  have hstable : (prefixWord ++ tailWord_1494581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494581).length < 2 ^ (prefixWord ++ tailWord_1494581).sum := by decide
  have hdescent : baseEnd_1494581 < baseStart_1494581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494585 : List Nat := [1, 2, 1, 5, 1, 4, 2, 2, 5]
def baseStart_1494585 : Nat := 118140960795 + 1494585 * 2 ^ 59
def prefixEnd_1494585 : Nat := 4983230072969 + 3 ^ 40 * 1494585 * 2
def baseEnd_1494585 : Nat := 85271164888904462557115

theorem tailTrace_1494585 : CollatzResearch.WordTrace tailWord_1494585 prefixEnd_1494585 85271164888904462557115 := by
  unfold tailWord_1494585
  simp only [CollatzResearch.WordTrace]
  refine ⟨54511993290381274641237209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36341328860254183094158139 54511993290381274641237209)
  ·
    refine ⟨40883994967785955980927907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54511993290381274641237209 40883994967785955980927907)
    ·
      refine ⟨61325992451678933971391861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40883994967785955980927907 61325992451678933971391861)
      ·
        refine ⟨5749311792344900059817987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61325992451678933971391861 5749311792344900059817987)
        ·
          refine ⟨8623967688517350089726981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5749311792344900059817987 8623967688517350089726981)
          ·
            refine ⟨1616993941597003141823809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8623967688517350089726981 1616993941597003141823809)
            ·
              refine ⟨1212745456197752356367857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1616993941597003141823809 1212745456197752356367857)
              ·
                refine ⟨909559092148314267275893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1212745456197752356367857 909559092148314267275893)
                ·
                  refine ⟨85271164888904462557115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 909559092148314267275893 85271164888904462557115)
                  ·
                    rfl

theorem cell23_1494585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 2, 2, 5].length) (baseStart_1494585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1494585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1494585 prefixEnd_1494585 := by exact prefixLift 1494585
  have htrace : WordTrace (prefixWord ++ tailWord_1494585) baseStart_1494585 baseEnd_1494585 := by
    simpa [prefixWord, tailWord_1494585, baseEnd_1494585] using wordTrace_append hprefix tailTrace_1494585
  have hstable : (prefixWord ++ tailWord_1494585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494585).length < 2 ^ (prefixWord ++ tailWord_1494585).sum := by decide
  have hdescent : baseEnd_1494585 < baseStart_1494585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494624 : List Nat := [2, 1, 1, 3, 2, 1, 1, 4, 8]
def baseStart_1494624 : Nat := 118140960795 + 1494624 * 2 ^ 59
def prefixEnd_1494624 : Nat := 4983230072969 + 3 ^ 40 * 1494624 * 2
def baseEnd_1494624 : Nat := 85273389971740612269595

theorem tailTrace_1494624 : CollatzResearch.WordTrace tailWord_1494624 prefixEnd_1494624 85273389971740612269595 := by
  unfold tailWord_1494624
  simp only [CollatzResearch.WordTrace]
  refine ⟨27256707868619992150953463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36342277158159989534604617 27256707868619992150953463)
  ·
    refine ⟨40885061802929988226430195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27256707868619992150953463 40885061802929988226430195)
    ·
      refine ⟨61327592704394982339645293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40885061802929988226430195 61327592704394982339645293)
      ·
        refine ⟨22997847264148118377366985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61327592704394982339645293 22997847264148118377366985)
        ·
          refine ⟨17248385448111088783025239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22997847264148118377366985 17248385448111088783025239)
          ·
            refine ⟨25872578172166633174537859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17248385448111088783025239 25872578172166633174537859)
            ·
              refine ⟨38808867258249949761806789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25872578172166633174537859 38808867258249949761806789)
              ·
                refine ⟨7276662610921865580338773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38808867258249949761806789 7276662610921865580338773)
                ·
                  refine ⟨85273389971740612269595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7276662610921865580338773 85273389971740612269595)
                  ·
                    rfl

theorem cell23_1494624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 8].length) (baseStart_1494624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1494624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1494624 prefixEnd_1494624 := by exact prefixLift 1494624
  have htrace : WordTrace (prefixWord ++ tailWord_1494624) baseStart_1494624 baseEnd_1494624 := by
    simpa [prefixWord, tailWord_1494624, baseEnd_1494624] using wordTrace_append hprefix tailTrace_1494624
  have hstable : (prefixWord ++ tailWord_1494624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494624).length < 2 ^ (prefixWord ++ tailWord_1494624).sum := by decide
  have hdescent : baseEnd_1494624 < baseStart_1494624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494645 : List Nat := [1, 3, 4, 2, 1, 2, 2, 1, 3, 4]
def baseStart_1494645 : Nat := 118140960795 + 1494645 * 2 ^ 59
def prefixEnd_1494645 : Nat := 4983230072969 + 3 ^ 40 * 1494645 * 2
def baseEnd_1494645 : Nat := 255823764279803309421253

theorem tailTrace_1494645 : CollatzResearch.WordTrace tailWord_1494645 prefixEnd_1494645 255823764279803309421253 := by
  unfold tailWord_1494645
  simp only [CollatzResearch.WordTrace]
  refine ⟨54514181670163904888421389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36342787780109269925614259 54514181670163904888421389)
  ·
    refine ⟨20442818126311464333158021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54514181670163904888421389 20442818126311464333158021)
    ·
      refine ⟨3833028398683399562467129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20442818126311464333158021 3833028398683399562467129)
      ·
        refine ⟨2874771299012549671850347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3833028398683399562467129 2874771299012549671850347)
        ·
          refine ⟨4312156948518824507775521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2874771299012549671850347 4312156948518824507775521)
          ·
            refine ⟨3234117711389118380831641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4312156948518824507775521 3234117711389118380831641)
            ·
              refine ⟨2425588283541838785623731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3234117711389118380831641 2425588283541838785623731)
              ·
                refine ⟨3638382425312758178435597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2425588283541838785623731 3638382425312758178435597)
                ·
                  refine ⟨1364393409492284316913349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3638382425312758178435597 1364393409492284316913349)
                  ·
                    refine ⟨255823764279803309421253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1364393409492284316913349 255823764279803309421253)
                    ·
                      rfl

theorem cell23_1494645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_1494645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1494645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1494645 prefixEnd_1494645 := by exact prefixLift 1494645
  have htrace : WordTrace (prefixWord ++ tailWord_1494645) baseStart_1494645 baseEnd_1494645 := by
    simpa [prefixWord, tailWord_1494645, baseEnd_1494645] using wordTrace_append hprefix tailTrace_1494645
  have hstable : (prefixWord ++ tailWord_1494645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494645).length < 2 ^ (prefixWord ++ tailWord_1494645).sum := by decide
  have hdescent : baseEnd_1494645 < baseStart_1494645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494668 : List Nat := [2, 2, 1, 2, 1, 1, 3, 4, 3, 1, 3]
def baseStart_1494668 : Nat := 118140960795 + 1494668 * 2 ^ 59
def prefixEnd_1494668 : Nat := 4983230072969 + 3 ^ 40 * 1494668 * 2
def baseEnd_1494668 : Nat := 767483102894463338276153

theorem tailTrace_1494668 : CollatzResearch.WordTrace tailWord_1494668 prefixEnd_1494668 767483102894463338276153 := by
  unfold tailWord_1494668
  simp only [CollatzResearch.WordTrace]
  refine ⟨27257510274540289908254329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36343347032720386544339105 27257510274540289908254329)
  ·
    refine ⟨20443132705905217431190747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27257510274540289908254329 20443132705905217431190747)
    ·
      refine ⟨30664699058857826146786121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20443132705905217431190747 30664699058857826146786121)
      ·
        refine ⟨22998524294143369610089591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30664699058857826146786121 22998524294143369610089591)
        ·
          refine ⟨34497786441215054415134387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22998524294143369610089591 34497786441215054415134387)
          ·
            refine ⟨51746679661822581622701581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34497786441215054415134387 51746679661822581622701581)
            ·
              refine ⟨19405004873183468108513093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51746679661822581622701581 19405004873183468108513093)
              ·
                refine ⟨3638438413721900270346205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19405004873183468108513093 3638438413721900270346205)
                ·
                  refine ⟨1364414405145712601379827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3638438413721900270346205 1364414405145712601379827)
                  ·
                    refine ⟨2046621607718568902069741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1364414405145712601379827 2046621607718568902069741)
                    ·
                      refine ⟨767483102894463338276153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2046621607718568902069741 767483102894463338276153)
                      ·
                        rfl

theorem cell23_1494668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 4, 3, 1, 3].length) (baseStart_1494668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1494668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1494668 prefixEnd_1494668 := by exact prefixLift 1494668
  have htrace : WordTrace (prefixWord ++ tailWord_1494668) baseStart_1494668 baseEnd_1494668 := by
    simpa [prefixWord, tailWord_1494668, baseEnd_1494668] using wordTrace_append hprefix tailTrace_1494668
  have hstable : (prefixWord ++ tailWord_1494668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494668).length < 2 ^ (prefixWord ++ tailWord_1494668).sum := by decide
  have hdescent : baseEnd_1494668 < baseStart_1494668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494688 : List Nat := [2, 1, 1, 4, 3, 1, 2, 3, 1, 5]
def baseStart_1494688 : Nat := 118140960795 + 1494688 * 2 ^ 59
def prefixEnd_1494688 : Nat := 4983230072969 + 3 ^ 40 * 1494688 * 2
def baseEnd_1494688 : Nat := 255831124169184420008687

theorem tailTrace_1494688 : CollatzResearch.WordTrace tailWord_1494688 prefixEnd_1494688 255831124169184420008687 := by
  unfold tailWord_1494688
  simp only [CollatzResearch.WordTrace]
  refine ⟨27257875004504061616118359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36343833339338748821491145 27257875004504061616118359)
  ·
    refine ⟨40886812506756092424177539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27257875004504061616118359 40886812506756092424177539)
    ·
      refine ⟨61330218760134138636266309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40886812506756092424177539 61330218760134138636266309)
      ·
        refine ⟨11499416017525150994299933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61330218760134138636266309 11499416017525150994299933)
        ·
          refine ⟨4312281006571931622862475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11499416017525150994299933 4312281006571931622862475)
          ·
            refine ⟨6468421509857897434293713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4312281006571931622862475 6468421509857897434293713)
            ·
              refine ⟨4851316132393423075720285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6468421509857897434293713 4851316132393423075720285)
              ·
                refine ⟨1819243549647533653395107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4851316132393423075720285 1819243549647533653395107)
                ·
                  refine ⟨2728865324471300480092661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1819243549647533653395107 2728865324471300480092661)
                  ·
                    refine ⟨255831124169184420008687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2728865324471300480092661 255831124169184420008687)
                    ·
                      rfl

theorem cell23_1494688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 3, 1, 5].length) (baseStart_1494688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1494688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1494688 prefixEnd_1494688 := by exact prefixLift 1494688
  have htrace : WordTrace (prefixWord ++ tailWord_1494688) baseStart_1494688 baseEnd_1494688 := by
    simpa [prefixWord, tailWord_1494688, baseEnd_1494688] using wordTrace_append hprefix tailTrace_1494688
  have hstable : (prefixWord ++ tailWord_1494688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494688).length < 2 ^ (prefixWord ++ tailWord_1494688).sum := by decide
  have hdescent : baseEnd_1494688 < baseStart_1494688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494696 : List Nat := [2, 1, 7, 1, 2, 1, 1, 1, 3, 4]
def baseStart_1494696 : Nat := 118140960795 + 1494696 * 2 ^ 59
def prefixEnd_1494696 : Nat := 4983230072969 + 3 ^ 40 * 1494696 * 2
def baseEnd_1494696 : Nat := 255832493450929742908675

theorem tailTrace_1494696 : CollatzResearch.WordTrace tailWord_1494696 prefixEnd_1494696 255832493450929742908675 := by
  unfold tailWord_1494696
  simp only [CollatzResearch.WordTrace]
  refine ⟨27258020896489570299263971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36344027861986093732351961 27258020896489570299263971)
  ·
    refine ⟨40887031344734355448895957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27258020896489570299263971 40887031344734355448895957)
    ·
      refine ⟨958289797142211455833499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 40887031344734355448895957 958289797142211455833499)
      ·
        refine ⟨1437434695713317183750249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 958289797142211455833499 1437434695713317183750249)
        ·
          refine ⟨1078076021784987887812687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1437434695713317183750249 1078076021784987887812687)
          ·
            refine ⟨1617114032677481831719031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1078076021784987887812687 1617114032677481831719031)
            ·
              refine ⟨2425671049016222747578547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1617114032677481831719031 2425671049016222747578547)
              ·
                refine ⟨3638506573524334121367821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2425671049016222747578547 3638506573524334121367821)
                ·
                  refine ⟨1364439965071625295512933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3638506573524334121367821 1364439965071625295512933)
                  ·
                    refine ⟨255832493450929742908675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1364439965071625295512933 255832493450929742908675)
                    ·
                      rfl

theorem cell23_1494696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_1494696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1494696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1494696 prefixEnd_1494696 := by exact prefixLift 1494696
  have htrace : WordTrace (prefixWord ++ tailWord_1494696) baseStart_1494696 baseEnd_1494696 := by
    simpa [prefixWord, tailWord_1494696, baseEnd_1494696] using wordTrace_append hprefix tailTrace_1494696
  have hstable : (prefixWord ++ tailWord_1494696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494696).length < 2 ^ (prefixWord ++ tailWord_1494696).sum := by decide
  have hdescent : baseEnd_1494696 < baseStart_1494696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494728 : List Nat := [2, 1, 3, 1, 2, 2, 3, 1, 3, 2, 3]
def baseStart_1494728 : Nat := 118140960795 + 1494728 * 2 ^ 59
def prefixEnd_1494728 : Nat := 4983230072969 + 3 ^ 40 * 1494728 * 2
def baseEnd_1494728 : Nat := 767513911733733103525877

theorem tailTrace_1494728 : CollatzResearch.WordTrace tailWord_1494728 prefixEnd_1494728 767513911733733103525877 := by
  unfold tailWord_1494728
  simp only [CollatzResearch.WordTrace]
  refine ⟨27258604464431605031846419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36344805952575473375795225 27258604464431605031846419)
  ·
    refine ⟨40887906696647407547769629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27258604464431605031846419 40887906696647407547769629)
    ·
      refine ⟨15332965011242777830413611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40887906696647407547769629 15332965011242777830413611)
      ·
        refine ⟨22999447516864166745620417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15332965011242777830413611 22999447516864166745620417)
        ·
          refine ⟨17249585637648125059215313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22999447516864166745620417 17249585637648125059215313)
          ·
            refine ⟨12937189228236093794411485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17249585637648125059215313 12937189228236093794411485)
            ·
              refine ⟨4851445960588535172904307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12937189228236093794411485 4851445960588535172904307)
              ·
                refine ⟨7277168940882802759356461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4851445960588535172904307 7277168940882802759356461)
                ·
                  refine ⟨2728938352831051034758673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7277168940882802759356461 2728938352831051034758673)
                  ·
                    refine ⟨2046703764623288276069005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2728938352831051034758673 2046703764623288276069005)
                    ·
                      refine ⟨767513911733733103525877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2046703764623288276069005 767513911733733103525877)
                      ·
                        rfl

theorem cell23_1494728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 3, 2, 3].length) (baseStart_1494728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1494728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1494728 prefixEnd_1494728 := by exact prefixLift 1494728
  have htrace : WordTrace (prefixWord ++ tailWord_1494728) baseStart_1494728 baseEnd_1494728 := by
    simpa [prefixWord, tailWord_1494728, baseEnd_1494728] using wordTrace_append hprefix tailTrace_1494728
  have hstable : (prefixWord ++ tailWord_1494728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494728).length < 2 ^ (prefixWord ++ tailWord_1494728).sum := by decide
  have hdescent : baseEnd_1494728 < baseStart_1494728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494738 : List Nat := [3, 2, 2, 2, 2, 1, 1, 1, 3, 2, 4]
def baseStart_1494738 : Nat := 118140960795 + 1494738 * 2 ^ 59
def prefixEnd_1494738 : Nat := 4983230072969 + 3 ^ 40 * 1494738 * 2
def baseEnd_1494738 : Nat := 767519046540278064400831

theorem tailTrace_1494738 : CollatzResearch.WordTrace tailWord_1494738 prefixEnd_1494738 767519046540278064400831 := by
  unfold tailWord_1494738
  simp only [CollatzResearch.WordTrace]
  refine ⟨13629393414706745442889217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36345049105884654514371245 13629393414706745442889217)
  ·
    refine ⟨10222045061030059082166913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13629393414706745442889217 10222045061030059082166913)
    ·
      refine ⟨7666533795772544311625185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10222045061030059082166913 7666533795772544311625185)
      ·
        refine ⟨5749900346829408233718889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7666533795772544311625185 5749900346829408233718889)
        ·
          refine ⟨4312425260122056175289167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5749900346829408233718889 4312425260122056175289167)
          ·
            refine ⟨6468637890183084262933751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4312425260122056175289167 6468637890183084262933751)
            ·
              refine ⟨9702956835274626394400627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6468637890183084262933751 9702956835274626394400627)
              ·
                refine ⟨14554435252911939591600941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9702956835274626394400627 14554435252911939591600941)
                ·
                  refine ⟨5457913219841977346850353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14554435252911939591600941 5457913219841977346850353)
                  ·
                    refine ⟨4093434914881483010137765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5457913219841977346850353 4093434914881483010137765)
                    ·
                      refine ⟨767519046540278064400831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4093434914881483010137765 767519046540278064400831)
                      ·
                        rfl

theorem cell23_1494738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_1494738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1494738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1494738 prefixEnd_1494738 := by exact prefixLift 1494738
  have htrace : WordTrace (prefixWord ++ tailWord_1494738) baseStart_1494738 baseEnd_1494738 := by
    simpa [prefixWord, tailWord_1494738, baseEnd_1494738] using wordTrace_append hprefix tailTrace_1494738
  have hstable : (prefixWord ++ tailWord_1494738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494738).length < 2 ^ (prefixWord ++ tailWord_1494738).sum := by decide
  have hdescent : baseEnd_1494738 < baseStart_1494738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494748 : List Nat := [2, 2, 5, 1, 2, 11]
def baseStart_1494748 : Nat := 118140960795 + 1494748 * 2 ^ 59
def prefixEnd_1494748 : Nat := 4983230072969 + 3 ^ 40 * 1494748 * 2
def baseEnd_1494748 : Nat := 3158535725707090638995

theorem tailTrace_1494748 : CollatzResearch.WordTrace tailWord_1494748 prefixEnd_1494748 3158535725707090638995 := by
  unfold tailWord_1494748
  simp only [CollatzResearch.WordTrace]
  refine ⟨27258969194395376739710449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36345292259193835652947265 27258969194395376739710449)
  ·
    refine ⟨20444226895796532554782837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27258969194395376739710449 20444226895796532554782837)
    ·
      refine ⟨1916646271480924927010891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20444226895796532554782837 1916646271480924927010891)
      ·
        refine ⟨2874969407221387390516337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1916646271480924927010891 2874969407221387390516337)
        ·
          refine ⟨2156227055416040542887253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2874969407221387390516337 2156227055416040542887253)
          ·
            refine ⟨3158535725707090638995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 2156227055416040542887253 3158535725707090638995)
            ·
              rfl

theorem cell23_1494748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 11].length) (baseStart_1494748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1494748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1494748 prefixEnd_1494748 := by exact prefixLift 1494748
  have htrace : WordTrace (prefixWord ++ tailWord_1494748) baseStart_1494748 baseEnd_1494748 := by
    simpa [prefixWord, tailWord_1494748, baseEnd_1494748] using wordTrace_append hprefix tailTrace_1494748
  have hstable : (prefixWord ++ tailWord_1494748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494748).length < 2 ^ (prefixWord ++ tailWord_1494748).sum := by decide
  have hdescent : baseEnd_1494748 < baseStart_1494748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494772 : List Nat := [2, 6, 1, 1, 1, 1, 1, 3, 1, 2, 4]
def baseStart_1494772 : Nat := 118140960795 + 1494772 * 2 ^ 59
def prefixEnd_1494772 : Nat := 4983230072969 + 3 ^ 40 * 1494772 * 2
def baseEnd_1494772 : Nat := 767536504882530931375675

theorem tailTrace_1494772 : CollatzResearch.WordTrace tailWord_1494772 prefixEnd_1494772 767536504882530931375675 := by
  unfold tailWord_1494772
  simp only [CollatzResearch.WordTrace]
  refine ⟨27259406870351902789147285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36345875827135870385529713 27259406870351902789147285)
  ·
    refine ⟨1277784697047745443241279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 27259406870351902789147285 1277784697047745443241279)
    ·
      refine ⟨1916677045571618164861919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1277784697047745443241279 1916677045571618164861919)
      ·
        refine ⟨2875015568357427247292879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1916677045571618164861919 2875015568357427247292879)
        ·
          refine ⟨4312523352536140870939319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2875015568357427247292879 4312523352536140870939319)
          ·
            refine ⟨6468785028804211306408979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4312523352536140870939319 6468785028804211306408979)
            ·
              refine ⟨9703177543206316959613469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6468785028804211306408979 9703177543206316959613469)
              ·
                refine ⟨3638691578702368859855051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9703177543206316959613469 3638691578702368859855051)
                ·
                  refine ⟨5458037368053553289782577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3638691578702368859855051 5458037368053553289782577)
                  ·
                    refine ⟨4093528026040164967336933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5458037368053553289782577 4093528026040164967336933)
                    ·
                      refine ⟨767536504882530931375675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4093528026040164967336933 767536504882530931375675)
                      ·
                        rfl

theorem cell23_1494772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_1494772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1494772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1494772 prefixEnd_1494772 := by exact prefixLift 1494772
  have htrace : WordTrace (prefixWord ++ tailWord_1494772) baseStart_1494772 baseEnd_1494772 := by
    simpa [prefixWord, tailWord_1494772, baseEnd_1494772] using wordTrace_append hprefix tailTrace_1494772
  have hstable : (prefixWord ++ tailWord_1494772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494772).length < 2 ^ (prefixWord ++ tailWord_1494772).sum := by decide
  have hdescent : baseEnd_1494772 < baseStart_1494772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494775 : List Nat := [1, 1, 3, 1, 1, 1, 6, 3, 2, 1, 3]
def baseStart_1494775 : Nat := 118140960795 + 1494775 * 2 ^ 59
def prefixEnd_1494775 : Nat := 4983230072969 + 3 ^ 40 * 1494775 * 2
def baseEnd_1494775 : Nat := 767538045324494419638161

theorem tailTrace_1494775 : CollatzResearch.WordTrace tailWord_1494775 prefixEnd_1494775 767538045324494419638161 := by
  unfold tailWord_1494775
  simp only [CollatzResearch.WordTrace]
  refine ⟨54518923159692937090653779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36345948773128624727102519 54518923159692937090653779)
  ·
    refine ⟨81778384739539405635980669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54518923159692937090653779 81778384739539405635980669)
    ·
      refine ⟨30666894277327277113492751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81778384739539405635980669 30666894277327277113492751)
      ·
        refine ⟨46000341415990915670239127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30666894277327277113492751 46000341415990915670239127)
        ·
          refine ⟨69000512123986373505358691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46000341415990915670239127 69000512123986373505358691)
          ·
            refine ⟨103500768185979560258038037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69000512123986373505358691 103500768185979560258038037)
            ·
              refine ⟨4851598508717791887095533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 103500768185979560258038037 4851598508717791887095533)
              ·
                refine ⟨1819349440769171957660825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4851598508717791887095533 1819349440769171957660825)
                ·
                  refine ⟨1364512080576878968245619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1819349440769171957660825 1364512080576878968245619)
                  ·
                    refine ⟨2046768120865318452368429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1364512080576878968245619 2046768120865318452368429)
                    ·
                      refine ⟨767538045324494419638161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2046768120865318452368429 767538045324494419638161)
                      ·
                        rfl

theorem cell23_1494775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 3, 2, 1, 3].length) (baseStart_1494775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1494775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1494775 prefixEnd_1494775 := by exact prefixLift 1494775
  have htrace : WordTrace (prefixWord ++ tailWord_1494775) baseStart_1494775 baseEnd_1494775 := by
    simpa [prefixWord, tailWord_1494775, baseEnd_1494775] using wordTrace_append hprefix tailTrace_1494775
  have hstable : (prefixWord ++ tailWord_1494775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494775).length < 2 ^ (prefixWord ++ tailWord_1494775).sum := by decide
  have hdescent : baseEnd_1494775 < baseStart_1494775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494785 : List Nat := [1, 2, 4, 1, 1, 1, 4, 1, 3, 3, 2]
def baseStart_1494785 : Nat := 118140960795 + 1494785 * 2 ^ 59
def prefixEnd_1494785 : Nat := 4983230072969 + 3 ^ 40 * 1494785 * 2
def baseEnd_1494785 : Nat := 767543180131039380513115

theorem tailTrace_1494785 : CollatzResearch.WordTrace tailWord_1494785 prefixEnd_1494785 767543180131039380513115 := by
  unfold tailWord_1494785
  simp only [CollatzResearch.WordTrace]
  refine ⟨54519287889656708798517809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36346191926437805865678539 54519287889656708798517809)
  ·
    refine ⟨40889465917242531598888357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54519287889656708798517809 40889465917242531598888357)
    ·
      refine ⟨7666774859482974674791567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40889465917242531598888357 7666774859482974674791567)
      ·
        refine ⟨11500162289224462012187351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7666774859482974674791567 11500162289224462012187351)
        ·
          refine ⟨17250243433836693018281027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11500162289224462012187351 17250243433836693018281027)
          ·
            refine ⟨25875365150755039527421541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17250243433836693018281027 25875365150755039527421541)
            ·
              refine ⟨4851630965766569911391539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25875365150755039527421541 4851630965766569911391539)
              ·
                refine ⟨7277446448649854867087309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4851630965766569911391539 7277446448649854867087309)
                ·
                  refine ⟨2729042418243695575157741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7277446448649854867087309 2729042418243695575157741)
                  ·
                    refine ⟨1023390906841385840684153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2729042418243695575157741 1023390906841385840684153)
                    ·
                      refine ⟨767543180131039380513115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1023390906841385840684153 767543180131039380513115)
                      ·
                        rfl

theorem cell23_1494785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 3, 3, 2].length) (baseStart_1494785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1494785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1494785 prefixEnd_1494785 := by exact prefixLift 1494785
  have htrace : WordTrace (prefixWord ++ tailWord_1494785) baseStart_1494785 baseEnd_1494785 := by
    simpa [prefixWord, tailWord_1494785, baseEnd_1494785] using wordTrace_append hprefix tailTrace_1494785
  have hstable : (prefixWord ++ tailWord_1494785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494785).length < 2 ^ (prefixWord ++ tailWord_1494785).sum := by decide
  have hdescent : baseEnd_1494785 < baseStart_1494785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494790 : List Nat := [6, 2, 2, 1, 1, 2, 2, 1, 1, 5]
def baseStart_1494790 : Nat := 118140960795 + 1494790 * 2 ^ 59
def prefixEnd_1494790 : Nat := 4983230072969 + 3 ^ 40 * 1494790 * 2
def baseEnd_1494790 : Nat := 255848582511437286983531

theorem tailTrace_1494790 : CollatzResearch.WordTrace tailWord_1494790 prefixEnd_1494790 255848582511437286983531 := by
  unfold tailWord_1494790
  simp only [CollatzResearch.WordTrace]
  refine ⟨1703733445457456082889057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 36346313503092396434966549 1703733445457456082889057)
  ·
    refine ⟨1277800084093092062166793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1703733445457456082889057 1277800084093092062166793)
    ·
      refine ⟨958350063069819046625095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1277800084093092062166793 958350063069819046625095)
      ·
        refine ⟨1437525094604728569937643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 958350063069819046625095 1437525094604728569937643)
        ·
          refine ⟨2156287641907092854906465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1437525094604728569937643 2156287641907092854906465)
          ·
            refine ⟨1617215731430319641179849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2156287641907092854906465 1617215731430319641179849)
            ·
              refine ⟨1212911798572739730884887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1617215731430319641179849 1212911798572739730884887)
              ·
                refine ⟨1819367697859109596327331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1212911798572739730884887 1819367697859109596327331)
                ·
                  refine ⟨2729051546788664394490997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1819367697859109596327331 2729051546788664394490997)
                  ·
                    refine ⟨255848582511437286983531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2729051546788664394490997 255848582511437286983531)
                    ·
                      rfl

theorem cell23_1494790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_1494790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1494790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1494790 prefixEnd_1494790 := by exact prefixLift 1494790
  have htrace : WordTrace (prefixWord ++ tailWord_1494790) baseStart_1494790 baseEnd_1494790 := by
    simpa [prefixWord, tailWord_1494790, baseEnd_1494790] using wordTrace_append hprefix tailTrace_1494790
  have hstable : (prefixWord ++ tailWord_1494790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494790).length < 2 ^ (prefixWord ++ tailWord_1494790).sum := by decide
  have hdescent : baseEnd_1494790 < baseStart_1494790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494801 : List Nat := [1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 5]
def baseStart_1494801 : Nat := 118140960795 + 1494801 * 2 ^ 59
def prefixEnd_1494801 : Nat := 4983230072969 + 3 ^ 40 * 1494801 * 2
def baseEnd_1494801 : Nat := 767551395821511317913041

theorem tailTrace_1494801 : CollatzResearch.WordTrace tailWord_1494801 prefixEnd_1494801 767551395821511317913041 := by
  unfold tailWord_1494801
  simp only [CollatzResearch.WordTrace]
  refine ⟨54519871457598743531100257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36346580971732495687400171 54519871457598743531100257)
  ·
    refine ⟨40889903593199057648325193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54519871457598743531100257 40889903593199057648325193)
    ·
      refine ⟨30667427694899293236243895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40889903593199057648325193 30667427694899293236243895)
      ·
        refine ⟨46001141542348939854365843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30667427694899293236243895 46001141542348939854365843)
        ·
          refine ⟨69001712313523409781548765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46001141542348939854365843 69001712313523409781548765)
          ·
            refine ⟨25875642117571278668080787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69001712313523409781548765 25875642117571278668080787)
            ·
              refine ⟨38813463176356918002121181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25875642117571278668080787 38813463176356918002121181)
              ·
                refine ⟨14555048691133844250795443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38813463176356918002121181 14555048691133844250795443)
                ·
                  refine ⟨21832573036700766376193165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14555048691133844250795443 21832573036700766376193165)
                  ·
                    refine ⟨8187214888762787391072437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21832573036700766376193165 8187214888762787391072437)
                    ·
                      refine ⟨767551395821511317913041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8187214888762787391072437 767551395821511317913041)
                      ·
                        rfl

theorem cell23_1494801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 5].length) (baseStart_1494801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1494801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1494801 prefixEnd_1494801 := by exact prefixLift 1494801
  have htrace : WordTrace (prefixWord ++ tailWord_1494801) baseStart_1494801 baseEnd_1494801 := by
    simpa [prefixWord, tailWord_1494801, baseEnd_1494801] using wordTrace_append hprefix tailTrace_1494801
  have hstable : (prefixWord ++ tailWord_1494801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494801).length < 2 ^ (prefixWord ++ tailWord_1494801).sum := by decide
  have hdescent : baseEnd_1494801 < baseStart_1494801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494811 : List Nat := [1, 1, 1, 1, 1, 1, 4, 2, 3, 4, 4]
def baseStart_1494811 : Nat := 118140960795 + 1494811 * 2 ^ 59
def prefixEnd_1494811 : Nat := 4983230072969 + 3 ^ 40 * 1494811 * 2
def baseEnd_1494811 : Nat := 767556530628056278787995

theorem tailTrace_1494811 : CollatzResearch.WordTrace tailWord_1494811 prefixEnd_1494811 767556530628056278787995 := by
  unfold tailWord_1494811
  simp only [CollatzResearch.WordTrace]
  refine ⟨54520236187562515238964287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36346824125041676825976191 54520236187562515238964287)
  ·
    refine ⟨81780354281343772858446431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54520236187562515238964287 81780354281343772858446431)
    ·
      refine ⟨122670531422015659287669647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81780354281343772858446431 122670531422015659287669647)
      ·
        refine ⟨184005797133023488931504471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122670531422015659287669647 184005797133023488931504471)
        ·
          refine ⟨276008695699535233397256707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184005797133023488931504471 276008695699535233397256707)
          ·
            refine ⟨414013043549302850095885061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276008695699535233397256707 414013043549302850095885061)
            ·
              refine ⟨77627445665494284392978449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 414013043549302850095885061 77627445665494284392978449)
              ·
                refine ⟨58220584249120713294733837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77627445665494284392978449 58220584249120713294733837)
                ·
                  refine ⟨21832719093420267485525189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58220584249120713294733837 21832719093420267485525189)
                  ·
                    refine ⟨4093634830016300153535973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21832719093420267485525189 4093634830016300153535973)
                    ·
                      refine ⟨767556530628056278787995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4093634830016300153535973 767556530628056278787995)
                      ·
                        rfl

theorem cell23_1494811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 4, 4].length) (baseStart_1494811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1494811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1494811 prefixEnd_1494811 := by exact prefixLift 1494811
  have htrace : WordTrace (prefixWord ++ tailWord_1494811) baseStart_1494811 baseEnd_1494811 := by
    simpa [prefixWord, tailWord_1494811, baseEnd_1494811] using wordTrace_append hprefix tailTrace_1494811
  have hstable : (prefixWord ++ tailWord_1494811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494811).length < 2 ^ (prefixWord ++ tailWord_1494811).sum := by decide
  have hdescent : baseEnd_1494811 < baseStart_1494811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494828 : List Nat := [2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 4]
def baseStart_1494828 : Nat := 118140960795 + 1494828 * 2 ^ 59
def prefixEnd_1494828 : Nat := 4983230072969 + 3 ^ 40 * 1494828 * 2
def baseEnd_1494828 : Nat := 767565259799182712275417

theorem tailTrace_1494828 : CollatzResearch.WordTrace tailWord_1494828 prefixEnd_1494828 767565259799182712275417 := by
  unfold tailWord_1494828
  simp only [CollatzResearch.WordTrace]
  refine ⟨27260428114250463571166569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36347237485667284761555425 27260428114250463571166569)
  ·
    refine ⟨20445321085687847678374927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27260428114250463571166569 20445321085687847678374927)
    ·
      refine ⟨30667981628531771517562391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20445321085687847678374927 30667981628531771517562391)
      ·
        refine ⟨46001972442797657276343587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30667981628531771517562391 46001972442797657276343587)
        ·
          refine ⟨69002958664196485914515381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46001972442797657276343587 69002958664196485914515381)
          ·
            refine ⟨6469027374768420554485817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69002958664196485914515381 6469027374768420554485817)
            ·
              refine ⟨4851770531076315415864363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6469027374768420554485817 4851770531076315415864363)
              ·
                refine ⟨7277655796614473123796545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4851770531076315415864363 7277655796614473123796545)
                ·
                  refine ⟨5458241847460854842847409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7277655796614473123796545 5458241847460854842847409)
                  ·
                    refine ⟨4093681385595641132135557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5458241847460854842847409 4093681385595641132135557)
                    ·
                      refine ⟨767565259799182712275417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4093681385595641132135557 767565259799182712275417)
                      ·
                        rfl

theorem cell23_1494828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 4].length) (baseStart_1494828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1494828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1494828 prefixEnd_1494828 := by exact prefixLift 1494828
  have htrace : WordTrace (prefixWord ++ tailWord_1494828) baseStart_1494828 baseEnd_1494828 := by
    simpa [prefixWord, tailWord_1494828, baseEnd_1494828] using wordTrace_append hprefix tailTrace_1494828
  have hstable : (prefixWord ++ tailWord_1494828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494828).length < 2 ^ (prefixWord ++ tailWord_1494828).sum := by decide
  have hdescent : baseEnd_1494828 < baseStart_1494828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494855 : List Nat := [1, 1, 4, 1, 2, 1, 5, 3, 5]
def baseStart_1494855 : Nat := 118140960795 + 1494855 * 2 ^ 59
def prefixEnd_1494855 : Nat := 4983230072969 + 3 ^ 40 * 1494855 * 2
def baseEnd_1494855 : Nat := 85286569308539345181977

theorem tailTrace_1494855 : CollatzResearch.WordTrace tailWord_1494855 prefixEnd_1494855 85286569308539345181977 := by
  unfold tailWord_1494855
  simp only [CollatzResearch.WordTrace]
  refine ⟨54521840999403110753566019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36347893999602073835710679 54521840999403110753566019)
  ·
    refine ⟨81782761499104666130349029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54521840999403110753566019 81782761499104666130349029)
    ·
      refine ⟨15334267781082124899440443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81782761499104666130349029 15334267781082124899440443)
      ·
        refine ⟨23001401671623187349160665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15334267781082124899440443 23001401671623187349160665)
        ·
          refine ⟨17251051253717390511870499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23001401671623187349160665 17251051253717390511870499)
          ·
            refine ⟨25876576880576085767805749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17251051253717390511870499 25876576880576085767805749)
            ·
              refine ⟨2425929082554008040731789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25876576880576085767805749 2425929082554008040731789)
              ·
                refine ⟨909723405957753015274421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2425929082554008040731789 909723405957753015274421)
                ·
                  refine ⟨85286569308539345181977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 909723405957753015274421 85286569308539345181977)
                  ·
                    rfl

theorem cell23_1494855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 3, 5].length) (baseStart_1494855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1494855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1494855 prefixEnd_1494855 := by exact prefixLift 1494855
  have htrace : WordTrace (prefixWord ++ tailWord_1494855) baseStart_1494855 baseEnd_1494855 := by
    simpa [prefixWord, tailWord_1494855, baseEnd_1494855] using wordTrace_append hprefix tailTrace_1494855
  have hstable : (prefixWord ++ tailWord_1494855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494855).length < 2 ^ (prefixWord ++ tailWord_1494855).sum := by decide
  have hdescent : baseEnd_1494855 < baseStart_1494855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494883 : List Nat := [1, 1, 1, 5, 5, 1, 2, 1, 2, 2, 2]
def baseStart_1494883 : Nat := 118140960795 + 1494883 * 2 ^ 59
def prefixEnd_1494883 : Nat := 4983230072969 + 3 ^ 40 * 1494883 * 2
def baseEnd_1494883 : Nat := 767593501235179997087665

theorem tailTrace_1494883 : CollatzResearch.WordTrace tailWord_1494883 prefixEnd_1494883 767593501235179997087665 := by
  unfold tailWord_1494883
  simp only [CollatzResearch.WordTrace]
  refine ⟨54522862243301671535585303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36348574828867781023723535 54522862243301671535585303)
  ·
    refine ⟨81784293364952507303377955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54522862243301671535585303 81784293364952507303377955)
    ·
      refine ⟨122676440047428760955066933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81784293364952507303377955 122676440047428760955066933)
      ·
        refine ⟨11500916254446446339537525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 122676440047428760955066933 11500916254446446339537525)
        ·
          refine ⟨1078210898854354344331643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11500916254446446339537525 1078210898854354344331643)
          ·
            refine ⟨1617316348281531516497465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1078210898854354344331643 1617316348281531516497465)
            ·
              refine ⟨1212987261211148637373099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1617316348281531516497465 1212987261211148637373099)
              ·
                refine ⟨1819480891816722956059649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1212987261211148637373099 1819480891816722956059649)
                ·
                  refine ⟨1364610668862542217044737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1819480891816722956059649 1364610668862542217044737)
                  ·
                    refine ⟨1023458001646906662783553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1364610668862542217044737 1023458001646906662783553)
                    ·
                      refine ⟨767593501235179997087665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1023458001646906662783553 767593501235179997087665)
                      ·
                        rfl

theorem cell23_1494883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 2, 1, 2, 2, 2].length) (baseStart_1494883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1494883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1494883 prefixEnd_1494883 := by exact prefixLift 1494883
  have htrace : WordTrace (prefixWord ++ tailWord_1494883) baseStart_1494883 baseEnd_1494883 := by
    simpa [prefixWord, tailWord_1494883, baseEnd_1494883] using wordTrace_append hprefix tailTrace_1494883
  have hstable : (prefixWord ++ tailWord_1494883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494883).length < 2 ^ (prefixWord ++ tailWord_1494883).sum := by decide
  have hdescent : baseEnd_1494883 < baseStart_1494883 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494905 : List Nat := [1, 2, 1, 3, 2, 2, 4, 1, 2, 1, 4]
def baseStart_1494905 : Nat := 118140960795 + 1494905 * 2 ^ 59
def prefixEnd_1494905 : Nat := 4983230072969 + 3 ^ 40 * 1494905 * 2
def baseEnd_1494905 : Nat := 767604797809578911012563

theorem tailTrace_1494905 : CollatzResearch.WordTrace tailWord_1494905 prefixEnd_1494905 767604797809578911012563 := by
  unfold tailWord_1494905
  simp only [CollatzResearch.WordTrace]
  refine ⟨54523664649221969292886169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36349109766147979528590779 54523664649221969292886169)
  ·
    refine ⟨40892748486916476969664627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54523664649221969292886169 40892748486916476969664627)
    ·
      refine ⟨61339122730374715454496941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40892748486916476969664627 61339122730374715454496941)
      ·
        refine ⟨23002171023890518295436353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61339122730374715454496941 23002171023890518295436353)
        ·
          refine ⟨17251628267917888721577265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23002171023890518295436353 17251628267917888721577265)
          ·
            refine ⟨12938721200938416541182949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17251628267917888721577265 12938721200938416541182949)
            ·
              refine ⟨2426010225175953101471803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12938721200938416541182949 2426010225175953101471803)
              ·
                refine ⟨3639015337763929652207705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2426010225175953101471803 3639015337763929652207705)
                ·
                  refine ⟨2729261503322947239155779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3639015337763929652207705 2729261503322947239155779)
                  ·
                    refine ⟨4093892254984420858733669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2729261503322947239155779 4093892254984420858733669)
                    ·
                      refine ⟨767604797809578911012563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4093892254984420858733669 767604797809578911012563)
                      ·
                        rfl

theorem cell23_1494905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 1, 2, 1, 4].length) (baseStart_1494905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1494905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1494905 prefixEnd_1494905 := by exact prefixLift 1494905
  have htrace : WordTrace (prefixWord ++ tailWord_1494905) baseStart_1494905 baseEnd_1494905 := by
    simpa [prefixWord, tailWord_1494905, baseEnd_1494905] using wordTrace_append hprefix tailTrace_1494905
  have hstable : (prefixWord ++ tailWord_1494905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494905).length < 2 ^ (prefixWord ++ tailWord_1494905).sum := by decide
  have hdescent : baseEnd_1494905 < baseStart_1494905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494928 : List Nat := [2, 1, 1, 1, 1, 1, 2, 8, 6]
def baseStart_1494928 : Nat := 118140960795 + 1494928 * 2 ^ 59
def prefixEnd_1494928 : Nat := 4983230072969 + 3 ^ 40 * 1494928 * 2
def baseEnd_1494928 : Nat := 85290734207181369002773

theorem tailTrace_1494928 : CollatzResearch.WordTrace tailWord_1494928 prefixEnd_1494928 85290734207181369002773 := by
  unfold tailWord_1494928
  simp only [CollatzResearch.WordTrace]
  refine ⟨27262251764069322110486719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36349669018759096147315625 27262251764069322110486719)
  ·
    refine ⟨40893377646103983165730079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27262251764069322110486719 40893377646103983165730079)
    ·
      refine ⟨61340066469155974748595119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40893377646103983165730079 61340066469155974748595119)
      ·
        refine ⟨92010099703733962122892679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61340066469155974748595119 92010099703733962122892679)
        ·
          refine ⟨138015149555600943184339019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92010099703733962122892679 138015149555600943184339019)
          ·
            refine ⟨207022724333401414776508529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138015149555600943184339019 207022724333401414776508529)
            ·
              refine ⟨155267043250051061082381397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 207022724333401414776508529 155267043250051061082381397)
              ·
                refine ⟨1819535663086535872059157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 155267043250051061082381397 1819535663086535872059157)
                ·
                  refine ⟨85290734207181369002773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1819535663086535872059157 85290734207181369002773)
                  ·
                    rfl

theorem cell23_1494928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 8, 6].length) (baseStart_1494928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1494928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1494928 prefixEnd_1494928 := by exact prefixLift 1494928
  have htrace : WordTrace (prefixWord ++ tailWord_1494928) baseStart_1494928 baseEnd_1494928 := by
    simpa [prefixWord, tailWord_1494928, baseEnd_1494928] using wordTrace_append hprefix tailTrace_1494928
  have hstable : (prefixWord ++ tailWord_1494928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494928).length < 2 ^ (prefixWord ++ tailWord_1494928).sum := by decide
  have hdescent : baseEnd_1494928 < baseStart_1494928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1494975 : List Nat := [1, 1, 2, 2, 2, 1, 5, 3, 1, 5]
def baseStart_1494975 : Nat := 118140960795 + 1494975 * 2 ^ 59
def prefixEnd_1494975 : Nat := 4983230072969 + 3 ^ 40 * 1494975 * 2
def baseEnd_1494975 : Nat := 255880247151797879045747

theorem tailTrace_1494975 : CollatzResearch.WordTrace tailWord_1494975 prefixEnd_1494975 255880247151797879045747 := by
  unfold tailWord_1494975
  simp only [CollatzResearch.WordTrace]
  refine ⟨54526217758968371247934379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36350811839312247498622919 54526217758968371247934379)
  ·
    refine ⟨81789326638452556871901569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54526217758968371247934379 81789326638452556871901569)
    ·
      refine ⟨61341994978839417653926177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81789326638452556871901569 61341994978839417653926177)
      ·
        refine ⟨46006496234129563240444633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61341994978839417653926177 46006496234129563240444633)
        ·
          refine ⟨34504872175597172430333475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46006496234129563240444633 34504872175597172430333475)
          ·
            refine ⟨51757308263395758645500213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34504872175597172430333475 51757308263395758645500213)
            ·
              refine ⟨4852247649693352373015645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51757308263395758645500213 4852247649693352373015645)
              ·
                refine ⟨1819592868635007139880867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4852247649693352373015645 1819592868635007139880867)
                ·
                  refine ⟨2729389302952510709821301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1819592868635007139880867 2729389302952510709821301)
                  ·
                    refine ⟨255880247151797879045747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2729389302952510709821301 255880247151797879045747)
                    ·
                      rfl

theorem cell23_1494975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 3, 1, 5].length) (baseStart_1494975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1494975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1494975 prefixEnd_1494975 := by exact prefixLift 1494975
  have htrace : WordTrace (prefixWord ++ tailWord_1494975) baseStart_1494975 baseEnd_1494975 := by
    simpa [prefixWord, tailWord_1494975, baseEnd_1494975] using wordTrace_append hprefix tailTrace_1494975
  have hstable : (prefixWord ++ tailWord_1494975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1494975).length < 2 ^ (prefixWord ++ tailWord_1494975).sum := by decide
  have hdescent : baseEnd_1494975 < baseStart_1494975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1494975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495012 : List Nat := [2, 3, 1, 1, 1, 1, 6, 2, 1, 1, 4]
def baseStart_1495012 : Nat := 118140960795 + 1495012 * 2 ^ 59
def prefixEnd_1495012 : Nat := 4983230072969 + 3 ^ 40 * 1495012 * 2
def baseEnd_1495012 : Nat := 767659740239609992374571

theorem tailTrace_1495012 : CollatzResearch.WordTrace tailWord_1495012 prefixEnd_1495012 767659740239609992374571 := by
  unfold tailWord_1495012
  simp only [CollatzResearch.WordTrace]
  refine ⟨27263783629917163283515645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36351711506556217711354193 27263783629917163283515645)
  ·
    refine ⟨10223918861218936231318367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27263783629917163283515645 10223918861218936231318367)
    ·
      refine ⟨15335878291828404346977551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10223918861218936231318367 15335878291828404346977551)
      ·
        refine ⟨23003817437742606520466327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15335878291828404346977551 23003817437742606520466327)
        ·
          refine ⟨34505726156613909780699491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23003817437742606520466327 34505726156613909780699491)
          ·
            refine ⟨51758589234920864671049237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34505726156613909780699491 51758589234920864671049237)
            ·
              refine ⟨2426183870386915531455433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 51758589234920864671049237 2426183870386915531455433)
              ·
                refine ⟨1819637902790186648591575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2426183870386915531455433 1819637902790186648591575)
                ·
                  refine ⟨2729456854185279972887363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1819637902790186648591575 2729456854185279972887363)
                  ·
                    refine ⟨4094185281277919959331045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2729456854185279972887363 4094185281277919959331045)
                    ·
                      refine ⟨767659740239609992374571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4094185281277919959331045 767659740239609992374571)
                      ·
                        rfl

theorem cell23_1495012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 2, 1, 1, 4].length) (baseStart_1495012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1495012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1495012 prefixEnd_1495012 := by exact prefixLift 1495012
  have htrace : WordTrace (prefixWord ++ tailWord_1495012) baseStart_1495012 baseEnd_1495012 := by
    simpa [prefixWord, tailWord_1495012, baseEnd_1495012] using wordTrace_append hprefix tailTrace_1495012
  have hstable : (prefixWord ++ tailWord_1495012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495012).length < 2 ^ (prefixWord ++ tailWord_1495012).sum := by decide
  have hdescent : baseEnd_1495012 < baseStart_1495012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495022 : List Nat := [4, 1, 2, 1, 3, 1, 1, 2, 4, 4]
def baseStart_1495022 : Nat := 118140960795 + 1495022 * 2 ^ 59
def prefixEnd_1495022 : Nat := 4983230072969 + 3 ^ 40 * 1495022 * 2
def baseEnd_1495022 : Nat := 255888291682051651083175

theorem tailTrace_1495022 : CollatzResearch.WordTrace tailWord_1495022 prefixEnd_1495022 255888291682051651083175 := by
  unfold tailWord_1495022
  simp only [CollatzResearch.WordTrace]
  refine ⟨6815991498724762284361915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36351954659865398849930213 6815991498724762284361915)
  ·
    refine ⟨10223987248087143426542873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6815991498724762284361915 10223987248087143426542873)
    ·
      refine ⟨7667990436065357569907155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10223987248087143426542873 7667990436065357569907155)
      ·
        refine ⟨11501985654098036354860733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7667990436065357569907155 11501985654098036354860733)
        ·
          refine ⟨4313244620286763633072775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11501985654098036354860733 4313244620286763633072775)
          ·
            refine ⟨6469866930430145449609163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4313244620286763633072775 6469866930430145449609163)
            ·
              refine ⟨9704800395645218174413745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6469866930430145449609163 9704800395645218174413745)
              ·
                refine ⟨7278600296733913630810309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9704800395645218174413745 7278600296733913630810309)
                ·
                  refine ⟨1364737555637608805776933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7278600296733913630810309 1364737555637608805776933)
                  ·
                    refine ⟨255888291682051651083175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1364737555637608805776933 255888291682051651083175)
                    ·
                      rfl

theorem cell23_1495022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 4, 4].length) (baseStart_1495022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1495022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1495022 prefixEnd_1495022 := by exact prefixLift 1495022
  have htrace : WordTrace (prefixWord ++ tailWord_1495022) baseStart_1495022 baseEnd_1495022 := by
    simpa [prefixWord, tailWord_1495022, baseEnd_1495022] using wordTrace_append hprefix tailTrace_1495022
  have hstable : (prefixWord ++ tailWord_1495022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495022).length < 2 ^ (prefixWord ++ tailWord_1495022).sum := by decide
  have hdescent : baseEnd_1495022 < baseStart_1495022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495032 : List Nat := [2, 1, 2, 1, 1, 3, 4, 3, 1, 2, 3]
def baseStart_1495032 : Nat := 118140960795 + 1495032 * 2 ^ 59
def prefixEnd_1495032 : Nat := 4983230072969 + 3 ^ 40 * 1495032 * 2
def baseEnd_1495032 : Nat := 767670009852699914124479

theorem tailTrace_1495032 : CollatzResearch.WordTrace tailWord_1495032 prefixEnd_1495032 767670009852699914124479 := by
  unfold tailWord_1495032
  simp only [CollatzResearch.WordTrace]
  refine ⟨27264148359880934991379675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36352197813174579988506233 27264148359880934991379675)
  ·
    refine ⟨40896222539821402487069513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27264148359880934991379675 40896222539821402487069513)
    ·
      refine ⟨30672166904866051865302135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40896222539821402487069513 30672166904866051865302135)
      ·
        refine ⟨46008250357299077797953203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30672166904866051865302135 46008250357299077797953203)
        ·
          refine ⟨69012375535948616696929805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46008250357299077797953203 69012375535948616696929805)
          ·
            refine ⟨25879640825980731261348677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69012375535948616696929805 25879640825980731261348677)
            ·
              refine ⟨4852432654871387111502877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25879640825980731261348677 4852432654871387111502877)
              ·
                refine ⟨1819662245576770166813579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4852432654871387111502877 1819662245576770166813579)
                ·
                  refine ⟨2729493368365155250220369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1819662245576770166813579 2729493368365155250220369)
                  ·
                    refine ⟨2047120026273866437665277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2729493368365155250220369 2047120026273866437665277)
                    ·
                      refine ⟨767670009852699914124479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2047120026273866437665277 767670009852699914124479)
                      ·
                        rfl

theorem cell23_1495032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 3, 1, 2, 3].length) (baseStart_1495032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1495032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1495032 prefixEnd_1495032 := by exact prefixLift 1495032
  have htrace : WordTrace (prefixWord ++ tailWord_1495032) baseStart_1495032 baseEnd_1495032 := by
    simpa [prefixWord, tailWord_1495032, baseEnd_1495032] using wordTrace_append hprefix tailTrace_1495032
  have hstable : (prefixWord ++ tailWord_1495032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495032).length < 2 ^ (prefixWord ++ tailWord_1495032).sum := by decide
  have hdescent : baseEnd_1495032 < baseStart_1495032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495096 : List Nat := [2, 1, 2, 1, 6, 1, 2, 2, 2, 1, 3]
def baseStart_1495096 : Nat := 118140960795 + 1495096 * 2 ^ 59
def prefixEnd_1495096 : Nat := 4983230072969 + 3 ^ 40 * 1495096 * 2
def baseEnd_1495096 : Nat := 767702872614587663724185

theorem tailTrace_1495096 : CollatzResearch.WordTrace tailWord_1495096 prefixEnd_1495096 767702872614587663724185 := by
  unfold tailWord_1495096
  simp only [CollatzResearch.WordTrace]
  refine ⟨27265315495765004456544571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36353753994353339275392761 27265315495765004456544571)
  ·
    refine ⟨40897973243647506684816857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27265315495765004456544571 40897973243647506684816857)
    ·
      refine ⟨30673479932735630013612643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40897973243647506684816857 30673479932735630013612643)
      ·
        refine ⟨46010219899103445020418965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30673479932735630013612643 46010219899103445020418965)
        ·
          refine ⟨2156729057770473985332139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 46010219899103445020418965 2156729057770473985332139)
          ·
            refine ⟨3235093586655710977998209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2156729057770473985332139 3235093586655710977998209)
            ·
              refine ⟨2426320189991783233498657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3235093586655710977998209 2426320189991783233498657)
              ·
                refine ⟨1819740142493837425123993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2426320189991783233498657 1819740142493837425123993)
                ·
                  refine ⟨1364805106870378068842995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1819740142493837425123993 1364805106870378068842995)
                  ·
                    refine ⟨2047207660305567103264493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1364805106870378068842995 2047207660305567103264493)
                    ·
                      refine ⟨767702872614587663724185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2047207660305567103264493 767702872614587663724185)
                      ·
                        rfl

theorem cell23_1495096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 2, 2, 1, 3].length) (baseStart_1495096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1495096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1495096 prefixEnd_1495096 := by exact prefixLift 1495096
  have htrace : WordTrace (prefixWord ++ tailWord_1495096) baseStart_1495096 baseEnd_1495096 := by
    simpa [prefixWord, tailWord_1495096, baseEnd_1495096] using wordTrace_append hprefix tailTrace_1495096
  have hstable : (prefixWord ++ tailWord_1495096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495096).length < 2 ^ (prefixWord ++ tailWord_1495096).sum := by decide
  have hdescent : baseEnd_1495096 < baseStart_1495096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495097 : List Nat := [1, 2, 1, 5, 4, 1, 2, 2, 1, 2, 2]
def baseStart_1495097 : Nat := 118140960795 + 1495097 * 2 ^ 59
def prefixEnd_1495097 : Nat := 4983230072969 + 3 ^ 40 * 1495097 * 2
def baseEnd_1495097 : Nat := 767703386095242159811681

theorem tailTrace_1495097 : CollatzResearch.WordTrace tailWord_1495097 prefixEnd_1495097 767703386095242159811681 := by
  unfold tailWord_1495097
  simp only [CollatzResearch.WordTrace]
  refine ⟨54530667464526386083875545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36353778309684257389250363 54530667464526386083875545)
  ·
    refine ⟨40898000598394789562906659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54530667464526386083875545 40898000598394789562906659)
    ·
      refine ⟨61347000897592184344359989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40898000598394789562906659 61347000897592184344359989)
      ·
        refine ⟨5751281334149267282283749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61347000897592184344359989 5751281334149267282283749)
        ·
          refine ⟨1078365250152987615428203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5751281334149267282283749 1078365250152987615428203)
          ·
            refine ⟨1617547875229481423142305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1078365250152987615428203 1617547875229481423142305)
            ·
              refine ⟨1213160906422111067356729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1617547875229481423142305 1213160906422111067356729)
              ·
                refine ⟨909870679816583300517547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1213160906422111067356729 909870679816583300517547)
                ·
                  refine ⟨1364806019724874950776321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 909870679816583300517547 1364806019724874950776321)
                  ·
                    refine ⟨1023604514793656213082241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1364806019724874950776321 1023604514793656213082241)
                    ·
                      refine ⟨767703386095242159811681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1023604514793656213082241 767703386095242159811681)
                      ·
                        rfl

theorem cell23_1495097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 2, 2, 1, 2, 2].length) (baseStart_1495097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1495097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1495097 prefixEnd_1495097 := by exact prefixLift 1495097
  have htrace : WordTrace (prefixWord ++ tailWord_1495097) baseStart_1495097 baseEnd_1495097 := by
    simpa [prefixWord, tailWord_1495097, baseEnd_1495097] using wordTrace_append hprefix tailTrace_1495097
  have hstable : (prefixWord ++ tailWord_1495097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495097).length < 2 ^ (prefixWord ++ tailWord_1495097).sum := by decide
  have hdescent : baseEnd_1495097 < baseStart_1495097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495115 : List Nat := [1, 1, 1, 1, 3, 1, 2, 5, 2, 2, 4]
def baseStart_1495115 : Nat := 118140960795 + 1495115 * 2 ^ 59
def prefixEnd_1495115 : Nat := 4983230072969 + 3 ^ 40 * 1495115 * 2
def baseEnd_1495115 : Nat := 767712628747023089386597

theorem tailTrace_1495115 : CollatzResearch.WordTrace tailWord_1495115 prefixEnd_1495115 767712628747023089386597 := by
  unfold tailWord_1495115
  simp only [CollatzResearch.WordTrace]
  refine ⟨54531323978461175158030799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36354215985640783438687199 54531323978461175158030799)
  ·
    refine ⟨81796985967691762737046199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54531323978461175158030799 81796985967691762737046199)
    ·
      refine ⟨122695478951537644105569299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81796985967691762737046199 122695478951537644105569299)
      ·
        refine ⟨184043218427306466158353949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122695478951537644105569299 184043218427306466158353949)
        ·
          refine ⟨69016206910239924809382731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184043218427306466158353949 69016206910239924809382731)
          ·
            refine ⟨103524310365359887214074097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69016206910239924809382731 103524310365359887214074097)
            ·
              refine ⟨77643232774019915410555573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103524310365359887214074097 77643232774019915410555573)
              ·
                refine ⟨7279053072564367069739585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77643232774019915410555573 7279053072564367069739585)
                ·
                  refine ⟨5459289804423275302304689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7279053072564367069739585 5459289804423275302304689)
                  ·
                    refine ⟨4094467353317456476728517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5459289804423275302304689 4094467353317456476728517)
                    ·
                      refine ⟨767712628747023089386597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4094467353317456476728517 767712628747023089386597)
                      ·
                        rfl

theorem cell23_1495115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 2, 2, 4].length) (baseStart_1495115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1495115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1495115 prefixEnd_1495115 := by exact prefixLift 1495115
  have htrace : WordTrace (prefixWord ++ tailWord_1495115) baseStart_1495115 baseEnd_1495115 := by
    simpa [prefixWord, tailWord_1495115, baseEnd_1495115] using wordTrace_append hprefix tailTrace_1495115
  have hstable : (prefixWord ++ tailWord_1495115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495115).length < 2 ^ (prefixWord ++ tailWord_1495115).sum := by decide
  have hdescent : baseEnd_1495115 < baseStart_1495115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495125 : List Nat := [1, 3, 2, 2, 1, 3, 1, 1, 9]
def baseStart_1495125 : Nat := 118140960795 + 1495125 * 2 ^ 59
def prefixEnd_1495125 : Nat := 4983230072969 + 3 ^ 40 * 1495125 * 2
def baseEnd_1495125 : Nat := 85301973728174227806839

theorem tailTrace_1495125 : CollatzResearch.WordTrace tailWord_1495125 prefixEnd_1495125 85301973728174227806839 := by
  unfold tailWord_1495125
  simp only [CollatzResearch.WordTrace]
  refine ⟨54531688708424946865894829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36354459138949964577263219 54531688708424946865894829)
  ·
    refine ⟨20449383265659355074710561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54531688708424946865894829 20449383265659355074710561)
    ·
      refine ⟨15337037449244516306032921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20449383265659355074710561 15337037449244516306032921)
      ·
        refine ⟨11502778086933387229524691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15337037449244516306032921 11502778086933387229524691)
        ·
          refine ⟨17254167130400080844287037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11502778086933387229524691 17254167130400080844287037)
          ·
            refine ⟨6470312673900030316607639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17254167130400080844287037 6470312673900030316607639)
            ·
              refine ⟨9705469010850045474911459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6470312673900030316607639 9705469010850045474911459)
              ·
                refine ⟨14558203516275068212367189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9705469010850045474911459 14558203516275068212367189)
                ·
                  refine ⟨85301973728174227806839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 14558203516275068212367189 85301973728174227806839)
                  ·
                    rfl

theorem cell23_1495125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 9].length) (baseStart_1495125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1495125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1495125 prefixEnd_1495125 := by exact prefixLift 1495125
  have htrace : WordTrace (prefixWord ++ tailWord_1495125) baseStart_1495125 baseEnd_1495125 := by
    simpa [prefixWord, tailWord_1495125, baseEnd_1495125] using wordTrace_append hprefix tailTrace_1495125
  have hstable : (prefixWord ++ tailWord_1495125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495125).length < 2 ^ (prefixWord ++ tailWord_1495125).sum := by decide
  have hdescent : baseEnd_1495125 < baseStart_1495125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495152 : List Nat := [2, 1, 1, 1, 5, 2, 1, 2, 2, 3, 3]
def baseStart_1495152 : Nat := 118140960795 + 1495152 * 2 ^ 59
def prefixEnd_1495152 : Nat := 4983230072969 + 3 ^ 40 * 1495152 * 2
def baseEnd_1495152 : Nat := 767731627531239444623927

theorem tailTrace_1495152 : CollatzResearch.WordTrace tailWord_1495152 prefixEnd_1495152 767731627531239444623927 := by
  unfold tailWord_1495152
  simp only [CollatzResearch.WordTrace]
  refine ⟨27266336739663565238563855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36355115652884753651418473 27266336739663565238563855)
  ·
    refine ⟨40899505109495347857845783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27266336739663565238563855 40899505109495347857845783)
    ·
      refine ⟨61349257664243021786768675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40899505109495347857845783 61349257664243021786768675)
      ·
        refine ⟨92023886496364532680153013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61349257664243021786768675 92023886496364532680153013)
        ·
          refine ⟨8627239359034174938764345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 92023886496364532680153013 8627239359034174938764345)
          ·
            refine ⟨6470429519275631204073259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8627239359034174938764345 6470429519275631204073259)
            ·
              refine ⟨9705644278913446806109889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6470429519275631204073259 9705644278913446806109889)
              ·
                refine ⟨7279233209185085104582417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9705644278913446806109889 7279233209185085104582417)
                ·
                  refine ⟨5459424906888813828436813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7279233209185085104582417 5459424906888813828436813)
                  ·
                    refine ⟨2047284340083305185663805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5459424906888813828436813 2047284340083305185663805)
                    ·
                      refine ⟨767731627531239444623927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2047284340083305185663805 767731627531239444623927)
                      ·
                        rfl

theorem cell23_1495152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 2, 3, 3].length) (baseStart_1495152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1495152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1495152 prefixEnd_1495152 := by exact prefixLift 1495152
  have htrace : WordTrace (prefixWord ++ tailWord_1495152) baseStart_1495152 baseEnd_1495152 := by
    simpa [prefixWord, tailWord_1495152, baseEnd_1495152] using wordTrace_append hprefix tailTrace_1495152
  have hstable : (prefixWord ++ tailWord_1495152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495152).length < 2 ^ (prefixWord ++ tailWord_1495152).sum := by decide
  have hdescent : baseEnd_1495152 < baseStart_1495152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495190 : List Nat := [5, 3, 2, 1, 1, 1, 1, 1, 2, 1, 5]
def baseStart_1495190 : Nat := 118140960795 + 1495190 * 2 ^ 59
def prefixEnd_1495190 : Nat := 4983230072969 + 3 ^ 40 * 1495190 * 2
def baseEnd_1495190 : Nat := 767751139796110295948753

theorem tailTrace_1495190 : CollatzResearch.WordTrace tailWord_1495190 prefixEnd_1495190 767751139796110295948753 := by
  unfold tailWord_1495190
  simp only [CollatzResearch.WordTrace]
  refine ⟨3408378715824341435438189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36356039635459641978007349 3408378715824341435438189)
  ·
    refine ⟨1278142018434128038289321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3408378715824341435438189 1278142018434128038289321)
    ·
      refine ⟨958606513825596028716991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1278142018434128038289321 958606513825596028716991)
      ·
        refine ⟨1437909770738394043075487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 958606513825596028716991 1437909770738394043075487)
        ·
          refine ⟨2156864656107591064613231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1437909770738394043075487 2156864656107591064613231)
          ·
            refine ⟨3235296984161386596919847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2156864656107591064613231 3235296984161386596919847)
            ·
              refine ⟨4852945476242079895379771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3235296984161386596919847 4852945476242079895379771)
              ·
                refine ⟨7279418214363119843069657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4852945476242079895379771 7279418214363119843069657)
                ·
                  refine ⟨5459563660772339882302243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7279418214363119843069657 5459563660772339882302243)
                  ·
                    refine ⟨8189345491158509823453365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5459563660772339882302243 8189345491158509823453365)
                    ·
                      refine ⟨767751139796110295948753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8189345491158509823453365 767751139796110295948753)
                      ·
                        rfl

theorem cell23_1495190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_1495190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1495190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1495190 prefixEnd_1495190 := by exact prefixLift 1495190
  have htrace : WordTrace (prefixWord ++ tailWord_1495190) baseStart_1495190 baseEnd_1495190 := by
    simpa [prefixWord, tailWord_1495190, baseEnd_1495190] using wordTrace_append hprefix tailTrace_1495190
  have hstable : (prefixWord ++ tailWord_1495190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495190).length < 2 ^ (prefixWord ++ tailWord_1495190).sum := by decide
  have hdescent : baseEnd_1495190 < baseStart_1495190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495235 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 8]
def baseStart_1495235 : Nat := 118140960795 + 1495235 * 2 ^ 59
def prefixEnd_1495235 : Nat := 4983230072969 + 3 ^ 40 * 1495235 * 2
def baseEnd_1495235 : Nat := 767774246425562619886045

theorem tailTrace_1495235 : CollatzResearch.WordTrace tailWord_1495235 prefixEnd_1495235 767774246425562619886045 := by
  unfold tailWord_1495235
  simp only [CollatzResearch.WordTrace]
  refine ⟨54535700738026435652399159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36357133825350957101599439 54535700738026435652399159)
  ·
    refine ⟨81803551107039653478598739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54535700738026435652399159 81803551107039653478598739)
    ·
      refine ⟨122705326660559480217898109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81803551107039653478598739 122705326660559480217898109)
      ·
        refine ⟨46014497497709805081711791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122705326660559480217898109 46014497497709805081711791)
        ·
          refine ⟨69021746246564707622567687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46014497497709805081711791 69021746246564707622567687)
          ·
            refine ⟨103532619369847061433851531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69021746246564707622567687 103532619369847061433851531)
            ·
              refine ⟨155298929054770592150777297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103532619369847061433851531 155298929054770592150777297)
              ·
                refine ⟨116474196791077944113082973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 155298929054770592150777297 116474196791077944113082973)
                ·
                  refine ⟨43677823796654229042406115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 116474196791077944113082973 43677823796654229042406115)
                  ·
                    refine ⟨65516735694981343563609173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43677823796654229042406115 65516735694981343563609173)
                    ·
                      refine ⟨767774246425562619886045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 65516735694981343563609173 767774246425562619886045)
                      ·
                        rfl

theorem cell23_1495235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 8].length) (baseStart_1495235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1495235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1495235 prefixEnd_1495235 := by exact prefixLift 1495235
  have htrace : WordTrace (prefixWord ++ tailWord_1495235) baseStart_1495235 baseEnd_1495235 := by
    simpa [prefixWord, tailWord_1495235, baseEnd_1495235] using wordTrace_append hprefix tailTrace_1495235
  have hstable : (prefixWord ++ tailWord_1495235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495235).length < 2 ^ (prefixWord ++ tailWord_1495235).sum := by decide
  have hdescent : baseEnd_1495235 < baseStart_1495235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495246 : List Nat := [4, 1, 1, 1, 4, 2, 2, 1, 2, 2, 3]
def baseStart_1495246 : Nat := 118140960795 + 1495246 * 2 ^ 59
def prefixEnd_1495246 : Nat := 4983230072969 + 3 ^ 40 * 1495246 * 2
def baseEnd_1495246 : Nat := 767779894712762076848495

theorem tailTrace_1495246 : CollatzResearch.WordTrace tailWord_1495246 prefixEnd_1495246 767779894712762076848495 := by
  unfold tailWord_1495246
  simp only [CollatzResearch.WordTrace]
  refine ⟨6817012742623323066381199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36357401293991056354033061 6817012742623323066381199)
  ·
    refine ⟨10225519113934984599571799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6817012742623323066381199 10225519113934984599571799)
    ·
      refine ⟨15338278670902476899357699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10225519113934984599571799 15338278670902476899357699)
      ·
        refine ⟨23007418006353715349036549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15338278670902476899357699 23007418006353715349036549)
        ·
          refine ⟨4313890876191321627944353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23007418006353715349036549 4313890876191321627944353)
          ·
            refine ⟨3235418157143491220958265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4313890876191321627944353 3235418157143491220958265)
            ·
              refine ⟨2426563617857618415718699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3235418157143491220958265 2426563617857618415718699)
              ·
                refine ⟨3639845426786427623578049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2426563617857618415718699 3639845426786427623578049)
                ·
                  refine ⟨2729884070089820717683537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3639845426786427623578049 2729884070089820717683537)
                  ·
                    refine ⟨2047413052567365538262653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2729884070089820717683537 2047413052567365538262653)
                    ·
                      refine ⟨767779894712762076848495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2047413052567365538262653 767779894712762076848495)
                      ·
                        rfl

theorem cell23_1495246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 1, 2, 2, 3].length) (baseStart_1495246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1495246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1495246 prefixEnd_1495246 := by exact prefixLift 1495246
  have htrace : WordTrace (prefixWord ++ tailWord_1495246) baseStart_1495246 baseEnd_1495246 := by
    simpa [prefixWord, tailWord_1495246, baseEnd_1495246] using wordTrace_append hprefix tailTrace_1495246
  have hstable : (prefixWord ++ tailWord_1495246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495246).length < 2 ^ (prefixWord ++ tailWord_1495246).sum := by decide
  have hdescent : baseEnd_1495246 < baseStart_1495246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495286 : List Nat := [5, 1, 1, 1, 1, 1, 2, 2, 4, 3, 2]
def baseStart_1495286 : Nat := 118140960795 + 1495286 * 2 ^ 59
def prefixEnd_1495286 : Nat := 4983230072969 + 3 ^ 40 * 1495286 * 2
def baseEnd_1495286 : Nat := 767800433938941920348311

theorem tailTrace_1495286 : CollatzResearch.WordTrace tailWord_1495286 prefixEnd_1495286 767800433938941920348311 := by
  unfold tailWord_1495286
  simp only [CollatzResearch.WordTrace]
  refine ⟨3408597553802604460156607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36358373907227780908337141 3408597553802604460156607)
  ·
    refine ⟨5112896330703906690234911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3408597553802604460156607 5112896330703906690234911)
    ·
      refine ⟨7669344496055860035352367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5112896330703906690234911 7669344496055860035352367)
      ·
        refine ⟨11504016744083790053028551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7669344496055860035352367 11504016744083790053028551)
        ·
          refine ⟨17256025116125685079542827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11504016744083790053028551 17256025116125685079542827)
          ·
            refine ⟨25884037674188527619314241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17256025116125685079542827 25884037674188527619314241)
            ·
              refine ⟨19413028255641395714485681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25884037674188527619314241 19413028255641395714485681)
              ·
                refine ⟨14559771191731046785864261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19413028255641395714485681 14559771191731046785864261)
                ·
                  refine ⟨2729957098449571272349549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14559771191731046785864261 2729957098449571272349549)
                  ·
                    refine ⟨1023733911918589227131081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2729957098449571272349549 1023733911918589227131081)
                    ·
                      refine ⟨767800433938941920348311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1023733911918589227131081 767800433938941920348311)
                      ·
                        rfl

theorem cell23_1495286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 4, 3, 2].length) (baseStart_1495286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1495286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1495286 prefixEnd_1495286 := by exact prefixLift 1495286
  have htrace : WordTrace (prefixWord ++ tailWord_1495286) baseStart_1495286 baseEnd_1495286 := by
    simpa [prefixWord, tailWord_1495286, baseEnd_1495286] using wordTrace_append hprefix tailTrace_1495286
  have hstable : (prefixWord ++ tailWord_1495286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495286).length < 2 ^ (prefixWord ++ tailWord_1495286).sum := by decide
  have hdescent : baseEnd_1495286 < baseStart_1495286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495299 : List Nat := [1, 1, 1, 3, 2, 3, 2, 4, 1, 1, 4]
def baseStart_1495299 : Nat := 118140960795 + 1495299 * 2 ^ 59
def prefixEnd_1495299 : Nat := 4983230072969 + 3 ^ 40 * 1495299 * 2
def baseEnd_1495299 : Nat := 767807109187450369485751

theorem tailTrace_1495299 : CollatzResearch.WordTrace tailWord_1495299 prefixEnd_1495299 767807109187450369485751 := by
  unfold tailWord_1495299
  simp only [CollatzResearch.WordTrace]
  refine ⟨54538035009794574582728951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36358690006529716388485967 54538035009794574582728951)
  ·
    refine ⟨81807052514691861874093427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54538035009794574582728951 81807052514691861874093427)
    ·
      refine ⟨122710578772037792811140141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81807052514691861874093427 122710578772037792811140141)
      ·
        refine ⟨46016467039514172304177553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122710578772037792811140141 46016467039514172304177553)
        ·
          refine ⟨34512350279635629228133165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46016467039514172304177553 34512350279635629228133165)
          ·
            refine ⟨12942131354863360960549937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34512350279635629228133165 12942131354863360960549937)
            ·
              refine ⟨9706598516147520720412453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12942131354863360960549937 9706598516147520720412453)
              ·
                refine ⟨1819987221777660135077335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9706598516147520720412453 1819987221777660135077335)
                ·
                  refine ⟨2729980832666490202616003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1819987221777660135077335 2729980832666490202616003)
                  ·
                    refine ⟨4094971248999735303924005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2729980832666490202616003 4094971248999735303924005)
                    ·
                      refine ⟨767807109187450369485751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4094971248999735303924005 767807109187450369485751)
                      ·
                        rfl

theorem cell23_1495299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 4, 1, 1, 4].length) (baseStart_1495299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1495299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1495299 prefixEnd_1495299 := by exact prefixLift 1495299
  have htrace : WordTrace (prefixWord ++ tailWord_1495299) baseStart_1495299 baseEnd_1495299 := by
    simpa [prefixWord, tailWord_1495299, baseEnd_1495299] using wordTrace_append hprefix tailTrace_1495299
  have hstable : (prefixWord ++ tailWord_1495299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495299).length < 2 ^ (prefixWord ++ tailWord_1495299).sum := by decide
  have hdescent : baseEnd_1495299 < baseStart_1495299 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495303 : List Nat := [1, 1, 4, 5, 1, 1, 1, 1, 1, 5, 2]
def baseStart_1495303 : Nat := 118140960795 + 1495303 * 2 ^ 59
def prefixEnd_1495303 : Nat := 4983230072969 + 3 ^ 40 * 1495303 * 2
def baseEnd_1495303 : Nat := 767809163110068353835733

theorem tailTrace_1495303 : CollatzResearch.WordTrace tailWord_1495303 prefixEnd_1495303 767809163110068353835733 := by
  unfold tailWord_1495303
  simp only [CollatzResearch.WordTrace]
  refine ⟨54538180901780083265874563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36358787267853388843916375 54538180901780083265874563)
  ·
    refine ⟨81807271352670124898811845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54538180901780083265874563 81807271352670124898811845)
    ·
      refine ⟨15338863378625648418527221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81807271352670124898811845 15338863378625648418527221)
      ·
        refine ⟨1438018441746154539236927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15338863378625648418527221 1438018441746154539236927)
        ·
          refine ⟨2157027662619231808855391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1438018441746154539236927 2157027662619231808855391)
          ·
            refine ⟨3235541493928847713283087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2157027662619231808855391 3235541493928847713283087)
            ·
              refine ⟨4853312240893271569924631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3235541493928847713283087 4853312240893271569924631)
              ·
                refine ⟨7279968361339907354886947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4853312240893271569924631 7279968361339907354886947)
                ·
                  refine ⟨10919952542009861032330421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7279968361339907354886947 10919952542009861032330421)
                  ·
                    refine ⟨1023745550813424471780977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10919952542009861032330421 1023745550813424471780977)
                    ·
                      refine ⟨767809163110068353835733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1023745550813424471780977 767809163110068353835733)
                      ·
                        rfl

theorem cell23_1495303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_1495303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1495303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1495303 prefixEnd_1495303 := by exact prefixLift 1495303
  have htrace : WordTrace (prefixWord ++ tailWord_1495303) baseStart_1495303 baseEnd_1495303 := by
    simpa [prefixWord, tailWord_1495303, baseEnd_1495303] using wordTrace_append hprefix tailTrace_1495303
  have hstable : (prefixWord ++ tailWord_1495303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495303).length < 2 ^ (prefixWord ++ tailWord_1495303).sum := by decide
  have hdescent : baseEnd_1495303 < baseStart_1495303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495336 : List Nat := [2, 1, 5, 1, 3, 1, 1, 2, 1, 1, 5]
def baseStart_1495336 : Nat := 118140960795 + 1495336 * 2 ^ 59
def prefixEnd_1495336 : Nat := 4983230072969 + 3 ^ 40 * 1495336 * 2
def baseEnd_1495336 : Nat := 767826107971666724723081

theorem tailTrace_1495336 : CollatzResearch.WordTrace tailWord_1495336 prefixEnd_1495336 767826107971666724723081 := by
  unfold tailWord_1495336
  simp only [CollatzResearch.WordTrace]
  refine ⟨27269692255330264950912931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36359589673773686601217241 27269692255330264950912931)
  ·
    refine ⟨40904538382995397426369397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27269692255330264950912931 40904538382995397426369397)
    ·
      refine ⟨3834800473405818508722131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40904538382995397426369397 3834800473405818508722131)
      ·
        refine ⟨5752200710108727763083197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3834800473405818508722131 5752200710108727763083197)
        ·
          refine ⟨2157075266290772911156199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5752200710108727763083197 2157075266290772911156199)
          ·
            refine ⟨3235612899436159366734299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2157075266290772911156199 3235612899436159366734299)
            ·
              refine ⟨4853419349154239050101449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3235612899436159366734299 4853419349154239050101449)
              ·
                refine ⟨3640064511865679287576087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4853419349154239050101449 3640064511865679287576087)
                ·
                  refine ⟨5460096767798518931364131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3640064511865679287576087 5460096767798518931364131)
                  ·
                    refine ⟨8190145151697778397046197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5460096767798518931364131 8190145151697778397046197)
                    ·
                      refine ⟨767826107971666724723081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8190145151697778397046197 767826107971666724723081)
                      ·
                        rfl

theorem cell23_1495336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_1495336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1495336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1495336 prefixEnd_1495336 := by exact prefixLift 1495336
  have htrace : WordTrace (prefixWord ++ tailWord_1495336) baseStart_1495336 baseEnd_1495336 := by
    simpa [prefixWord, tailWord_1495336, baseEnd_1495336] using wordTrace_append hprefix tailTrace_1495336
  have hstable : (prefixWord ++ tailWord_1495336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495336).length < 2 ^ (prefixWord ++ tailWord_1495336).sum := by decide
  have hdescent : baseEnd_1495336 < baseStart_1495336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495352 : List Nat := [2, 1, 2, 1, 3, 1, 2, 2, 2, 7]
def baseStart_1495352 : Nat := 118140960795 + 1495352 * 2 ^ 59
def prefixEnd_1495352 : Nat := 4983230072969 + 3 ^ 40 * 1495352 * 2
def baseEnd_1495352 : Nat := 255944774554046220707669

theorem tailTrace_1495352 : CollatzResearch.WordTrace tailWord_1495352 prefixEnd_1495352 255944774554046220707669 := by
  unfold tailWord_1495352
  simp only [CollatzResearch.WordTrace]
  refine ⟨27269984039301282317204155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36359978719068376422938873 27269984039301282317204155)
  ·
    refine ⟨40904976058951923475806233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27269984039301282317204155 40904976058951923475806233)
    ·
      refine ⟨30678732044213942606854675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40904976058951923475806233 30678732044213942606854675)
      ·
        refine ⟨46018098066320913910282013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30678732044213942606854675 46018098066320913910282013)
        ·
          refine ⟨17256786774870342716355755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46018098066320913910282013 17256786774870342716355755)
          ·
            refine ⟨25885180162305514074533633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17256786774870342716355755 25885180162305514074533633)
            ·
              refine ⟨19413885121729135555900225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25885180162305514074533633 19413885121729135555900225)
              ·
                refine ⟨14560413841296851666925169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19413885121729135555900225 14560413841296851666925169)
                ·
                  refine ⟨10920310380972638750193877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14560413841296851666925169 10920310380972638750193877)
                  ·
                    refine ⟨255944774554046220707669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10920310380972638750193877 255944774554046220707669)
                    ·
                      rfl

theorem cell23_1495352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 2, 7].length) (baseStart_1495352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1495352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1495352 prefixEnd_1495352 := by exact prefixLift 1495352
  have htrace : WordTrace (prefixWord ++ tailWord_1495352) baseStart_1495352 baseEnd_1495352 := by
    simpa [prefixWord, tailWord_1495352, baseEnd_1495352] using wordTrace_append hprefix tailTrace_1495352
  have hstable : (prefixWord ++ tailWord_1495352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495352).length < 2 ^ (prefixWord ++ tailWord_1495352).sum := by decide
  have hdescent : baseEnd_1495352 < baseStart_1495352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495353 : List Nat := [1, 2, 1, 6, 1, 2, 2, 2, 1, 2, 3]
def baseStart_1495353 : Nat := 118140960795 + 1495353 * 2 ^ 59
def prefixEnd_1495353 : Nat := 4983230072969 + 3 ^ 40 * 1495353 * 2
def baseEnd_1495353 : Nat := 767834837142793158210503

theorem tailTrace_1495353 : CollatzResearch.WordTrace tailWord_1495353 prefixEnd_1495353 767834837142793158210503 := by
  unfold tailWord_1495353
  simp only [CollatzResearch.WordTrace]
  refine ⟨54540004551598941805194713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36360003034399294536796475 54540004551598941805194713)
  ·
    refine ⟨40905003413699206353896035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54540004551598941805194713 40905003413699206353896035)
    ·
      refine ⟨61357505120548809530844053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40905003413699206353896035 61357505120548809530844053)
      ·
        refine ⟨2876133052525725446758315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 61357505120548809530844053 2876133052525725446758315)
        ·
          refine ⟨4314199578788588170137473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2876133052525725446758315 4314199578788588170137473)
          ·
            refine ⟨3235649684091441127603105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4314199578788588170137473 3235649684091441127603105)
            ·
              refine ⟨2426737263068580845702329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3235649684091441127603105 2426737263068580845702329)
              ·
                refine ⟨1820052947301435634276747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2426737263068580845702329 1820052947301435634276747)
                ·
                  refine ⟨2730079420952153451415121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1820052947301435634276747 2730079420952153451415121)
                  ·
                    refine ⟨2047559565714115088561341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2730079420952153451415121 2047559565714115088561341)
                    ·
                      refine ⟨767834837142793158210503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2047559565714115088561341 767834837142793158210503)
                      ·
                        rfl

theorem cell23_1495353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_1495353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1495353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1495353 prefixEnd_1495353 := by exact prefixLift 1495353
  have htrace : WordTrace (prefixWord ++ tailWord_1495353) baseStart_1495353 baseEnd_1495353 := by
    simpa [prefixWord, tailWord_1495353, baseEnd_1495353] using wordTrace_append hprefix tailTrace_1495353
  have hstable : (prefixWord ++ tailWord_1495353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495353).length < 2 ^ (prefixWord ++ tailWord_1495353).sum := by decide
  have hdescent : baseEnd_1495353 < baseStart_1495353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495400 : List Nat := [2, 1, 4, 2, 2, 1, 4, 1, 2, 1, 3]
def baseStart_1495400 : Nat := 118140960795 + 1495400 * 2 ^ 59
def prefixEnd_1495400 : Nat := 4983230072969 + 3 ^ 40 * 1495400 * 2
def baseEnd_1495400 : Nat := 767858970733554474322787

theorem tailTrace_1495400 : CollatzResearch.WordTrace tailWord_1495400 prefixEnd_1495400 767858970733554474322787 := by
  unfold tailWord_1495400
  simp only [CollatzResearch.WordTrace]
  refine ⟨27270859391214334416077827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36361145854952445888103769 27270859391214334416077827)
  ·
    refine ⟨40906289086821501624116741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27270859391214334416077827 40906289086821501624116741)
    ·
      refine ⟨7669929203779031554521889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40906289086821501624116741 7669929203779031554521889)
      ·
        refine ⟨5752446902834273665891417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7669929203779031554521889 5752446902834273665891417)
        ·
          refine ⟨4314335177125705249418563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5752446902834273665891417 4314335177125705249418563)
          ·
            refine ⟨6471502765688557874127845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4314335177125705249418563 6471502765688557874127845)
            ·
              refine ⟨1213406768566604601398971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6471502765688557874127845 1213406768566604601398971)
              ·
                refine ⟨1820110152849906902098457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1213406768566604601398971 1820110152849906902098457)
                ·
                  refine ⟨1365082614637430176573843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1820110152849906902098457 1365082614637430176573843)
                  ·
                    refine ⟨2047623921956145264860765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1365082614637430176573843 2047623921956145264860765)
                    ·
                      refine ⟨767858970733554474322787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2047623921956145264860765 767858970733554474322787)
                      ·
                        rfl

theorem cell23_1495400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 4, 1, 2, 1, 3].length) (baseStart_1495400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1495400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1495400 prefixEnd_1495400 := by exact prefixLift 1495400
  have htrace : WordTrace (prefixWord ++ tailWord_1495400) baseStart_1495400 baseEnd_1495400 := by
    simpa [prefixWord, tailWord_1495400, baseEnd_1495400] using wordTrace_append hprefix tailTrace_1495400
  have hstable : (prefixWord ++ tailWord_1495400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495400).length < 2 ^ (prefixWord ++ tailWord_1495400).sum := by decide
  have hdescent : baseEnd_1495400 < baseStart_1495400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495410 : List Nat := [3, 2, 1, 2, 1, 5, 1, 2, 1, 3, 2]
def baseStart_1495410 : Nat := 118140960795 + 1495410 * 2 ^ 59
def prefixEnd_1495410 : Nat := 4983230072969 + 3 ^ 40 * 1495410 * 2
def baseEnd_1495410 : Nat := 767864105540099435197741

theorem tailTrace_1495410 : CollatzResearch.WordTrace tailWord_1495410 prefixEnd_1495410 767864105540099435197741 := by
  unfold tailWord_1495410
  simp only [CollatzResearch.WordTrace]
  refine ⟨13635520878098110135004921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36361389008261627026679789 13635520878098110135004921)
  ·
    refine ⟨10226640658573582601253691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13635520878098110135004921 10226640658573582601253691)
    ·
      refine ⟨15339960987860373901880537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10226640658573582601253691 15339960987860373901880537)
      ·
        refine ⟨11504970740895280426410403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15339960987860373901880537 11504970740895280426410403)
        ·
          refine ⟨17257456111342920639615605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11504970740895280426410403 17257456111342920639615605)
          ·
            refine ⟨1617886510438398809963963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17257456111342920639615605 1617886510438398809963963)
            ·
              refine ⟨2426829765657598214945945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1617886510438398809963963 2426829765657598214945945)
              ·
                refine ⟨1820122324243198661209459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2426829765657598214945945 1820122324243198661209459)
                ·
                  refine ⟨2730183486364797991814189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1820122324243198661209459 2730183486364797991814189)
                  ·
                    refine ⟨1023818807386799246930321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2730183486364797991814189 1023818807386799246930321)
                    ·
                      refine ⟨767864105540099435197741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1023818807386799246930321 767864105540099435197741)
                      ·
                        rfl

theorem cell23_1495410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 2, 1, 3, 2].length) (baseStart_1495410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1495410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1495410 prefixEnd_1495410 := by exact prefixLift 1495410
  have htrace : WordTrace (prefixWord ++ tailWord_1495410) baseStart_1495410 baseEnd_1495410 := by
    simpa [prefixWord, tailWord_1495410, baseEnd_1495410] using wordTrace_append hprefix tailTrace_1495410
  have hstable : (prefixWord ++ tailWord_1495410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495410).length < 2 ^ (prefixWord ++ tailWord_1495410).sum := by decide
  have hdescent : baseEnd_1495410 < baseStart_1495410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495456 : List Nat := [2, 1, 1, 4, 1, 4, 1, 1, 2, 3, 3]
def baseStart_1495456 : Nat := 118140960795 + 1495456 * 2 ^ 59
def prefixEnd_1495456 : Nat := 4983230072969 + 3 ^ 40 * 1495456 * 2
def baseEnd_1495456 : Nat := 767887725650206255222529

theorem tailTrace_1495456 : CollatzResearch.WordTrace tailWord_1495456 prefixEnd_1495456 767887725650206255222529 := by
  unfold tailWord_1495456
  simp only [CollatzResearch.WordTrace]
  refine ⟨27271880635112895198097111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36362507513483860264129481 27271880635112895198097111)
  ·
    refine ⟨40907820952669342797145667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27271880635112895198097111 40907820952669342797145667)
    ·
      refine ⟨61361731429004014195718501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40907820952669342797145667 61361731429004014195718501)
      ·
        refine ⟨11505324642938252661697219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61361731429004014195718501 11505324642938252661697219)
        ·
          refine ⟨17257986964407378992545829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11505324642938252661697219 17257986964407378992545829)
          ·
            refine ⟨3235872555826383561102343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17257986964407378992545829 3235872555826383561102343)
            ·
              refine ⟨4853808833739575341653515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3235872555826383561102343 4853808833739575341653515)
              ·
                refine ⟨7280713250609363012480273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4853808833739575341653515 7280713250609363012480273)
                ·
                  refine ⟨5460534937957022259360205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7280713250609363012480273 5460534937957022259360205)
                  ·
                    refine ⟨2047700601733883347260077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5460534937957022259360205 2047700601733883347260077)
                    ·
                      refine ⟨767887725650206255222529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2047700601733883347260077 767887725650206255222529)
                      ·
                        rfl

theorem cell23_1495456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 2, 3, 3].length) (baseStart_1495456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1495456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1495456 prefixEnd_1495456 := by exact prefixLift 1495456
  have htrace : WordTrace (prefixWord ++ tailWord_1495456) baseStart_1495456 baseEnd_1495456 := by
    simpa [prefixWord, tailWord_1495456, baseEnd_1495456] using wordTrace_append hprefix tailTrace_1495456
  have hstable : (prefixWord ++ tailWord_1495456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495456).length < 2 ^ (prefixWord ++ tailWord_1495456).sum := by decide
  have hdescent : baseEnd_1495456 < baseStart_1495456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495533 : List Nat := [1, 5, 1, 3, 1, 1, 2, 1, 1, 4, 3]
def baseStart_1495533 : Nat := 118140960795 + 1495533 * 2 ^ 59
def prefixEnd_1495533 : Nat := 4983230072969 + 3 ^ 40 * 1495533 * 2
def baseEnd_1495533 : Nat := 767927263660602453959675

theorem tailTrace_1495533 : CollatzResearch.WordTrace tailWord_1495533 prefixEnd_1495533 767927263660602453959675 := by
  unfold tailWord_1495533
  simp only [CollatzResearch.WordTrace]
  refine ⟨54546569690946832546747253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36364379793964555031164835 54546569690946832546747253)
  ·
    refine ⟨5113740908526265551257555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54546569690946832546747253 5113740908526265551257555)
    ·
      refine ⟨7670611362789398326886333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5113740908526265551257555 7670611362789398326886333)
      ·
        refine ⟨2876479261046024372582375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7670611362789398326886333 2876479261046024372582375)
        ·
          refine ⟨4314718891569036558873563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2876479261046024372582375 4314718891569036558873563)
          ·
            refine ⟨6472078337353554838310345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4314718891569036558873563 6472078337353554838310345)
            ·
              refine ⟨4854058753015166128732759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6472078337353554838310345 4854058753015166128732759)
              ·
                refine ⟨7281088129522749193099139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4854058753015166128732759 7281088129522749193099139)
                ·
                  refine ⟨10921632194284123789648709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7281088129522749193099139 10921632194284123789648709)
                  ·
                    refine ⟨2047806036428273210559133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10921632194284123789648709 2047806036428273210559133)
                    ·
                      refine ⟨767927263660602453959675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2047806036428273210559133 767927263660602453959675)
                      ·
                        rfl

theorem cell23_1495533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_1495533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1495533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1495533 prefixEnd_1495533 := by exact prefixLift 1495533
  have htrace : WordTrace (prefixWord ++ tailWord_1495533) baseStart_1495533 baseEnd_1495533 := by
    simpa [prefixWord, tailWord_1495533, baseEnd_1495533] using wordTrace_append hprefix tailTrace_1495533
  have hstable : (prefixWord ++ tailWord_1495533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495533).length < 2 ^ (prefixWord ++ tailWord_1495533).sum := by decide
  have hdescent : baseEnd_1495533 < baseStart_1495533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495573 : List Nat := [1, 3, 2, 1, 3, 1, 1, 2, 4, 3, 2]
def baseStart_1495573 : Nat := 118140960795 + 1495573 * 2 ^ 59
def prefixEnd_1495573 : Nat := 4983230072969 + 3 ^ 40 * 1495573 * 2
def baseEnd_1495573 : Nat := 767947802886782297459491

theorem tailTrace_1495573 : CollatzResearch.WordTrace tailWord_1495573 prefixEnd_1495573 767947802886782297459491 := by
  unfold tailWord_1495573
  simp only [CollatzResearch.WordTrace]
  refine ⟨54548028610801919378203373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36365352407201279585468915 54548028610801919378203373)
  ·
    refine ⟨20455510729050719766826265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54548028610801919378203373 20455510729050719766826265)
    ·
      refine ⟨15341633046788039825119699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20455510729050719766826265 15341633046788039825119699)
      ·
        refine ⟨23012449570182059737679549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15341633046788039825119699 23012449570182059737679549)
        ·
          refine ⟨8629668588818272401629831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23012449570182059737679549 8629668588818272401629831)
          ·
            refine ⟨12944502883227408602444747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8629668588818272401629831 12944502883227408602444747)
            ·
              refine ⟨19416754324841112903667121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12944502883227408602444747 19416754324841112903667121)
              ·
                refine ⟨14562565743630834677750341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19416754324841112903667121 14562565743630834677750341)
                ·
                  refine ⟨2730481076930781502078189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14562565743630834677750341 2730481076930781502078189)
                  ·
                    refine ⟨1023930403849043063279321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2730481076930781502078189 1023930403849043063279321)
                    ·
                      refine ⟨767947802886782297459491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1023930403849043063279321 767947802886782297459491)
                      ·
                        rfl

theorem cell23_1495573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 4, 3, 2].length) (baseStart_1495573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1495573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1495573 prefixEnd_1495573 := by exact prefixLift 1495573
  have htrace : WordTrace (prefixWord ++ tailWord_1495573) baseStart_1495573 baseEnd_1495573 := by
    simpa [prefixWord, tailWord_1495573, baseEnd_1495573] using wordTrace_append hprefix tailTrace_1495573
  have hstable : (prefixWord ++ tailWord_1495573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495573).length < 2 ^ (prefixWord ++ tailWord_1495573).sum := by decide
  have hdescent : baseEnd_1495573 < baseStart_1495573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495579 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 7, 6]
def baseStart_1495579 : Nat := 118140960795 + 1495579 * 2 ^ 59
def prefixEnd_1495579 : Nat := 4983230072969 + 3 ^ 40 * 1495579 * 2
def baseEnd_1495579 : Nat := 255983627923569757994821

theorem tailTrace_1495579 : CollatzResearch.WordTrace tailWord_1495579 prefixEnd_1495579 255983627923569757994821 := by
  unfold tailWord_1495579
  simp only [CollatzResearch.WordTrace]
  refine ⟨54548247448780182402921791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36365498299186788268614527 54548247448780182402921791)
  ·
    refine ⟨81822371173170273604382687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54548247448780182402921791 81822371173170273604382687)
    ·
      refine ⟨122733556759755410406574031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81822371173170273604382687 122733556759755410406574031)
      ·
        refine ⟨184100335139633115609861047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122733556759755410406574031 184100335139633115609861047)
        ·
          refine ⟨276150502709449673414791571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184100335139633115609861047 276150502709449673414791571)
          ·
            refine ⟨414225754064174510122187357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276150502709449673414791571 414225754064174510122187357)
            ·
              refine ⟨155334657774065441295820259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 414225754064174510122187357 155334657774065441295820259)
              ·
                refine ⟨233001986661098161943730389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155334657774065441295820259 233001986661098161943730389)
                ·
                  refine ⟨5460984062369488170556181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 233001986661098161943730389 5460984062369488170556181)
                  ·
                    refine ⟨255983627923569757994821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5460984062369488170556181 255983627923569757994821)
                    ·
                      rfl

theorem cell23_1495579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 6].length) (baseStart_1495579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1495579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1495579 prefixEnd_1495579 := by exact prefixLift 1495579
  have htrace : WordTrace (prefixWord ++ tailWord_1495579) baseStart_1495579 baseEnd_1495579 := by
    simpa [prefixWord, tailWord_1495579, baseEnd_1495579] using wordTrace_append hprefix tailTrace_1495579
  have hstable : (prefixWord ++ tailWord_1495579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495579).length < 2 ^ (prefixWord ++ tailWord_1495579).sum := by decide
  have hdescent : baseEnd_1495579 < baseStart_1495579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495596 : List Nat := [2, 2, 1, 1, 1, 2, 1, 3, 6, 4]
def baseStart_1495596 : Nat := 118140960795 + 1495596 * 2 ^ 59
def prefixEnd_1495596 : Nat := 4983230072969 + 3 ^ 40 * 1495596 * 2
def baseEnd_1495596 : Nat := 255986537647278569157295

theorem tailTrace_1495596 : CollatzResearch.WordTrace tailWord_1495596 prefixEnd_1495596 255986537647278569157295 := by
  unfold tailWord_1495596
  simp only [CollatzResearch.WordTrace]
  refine ⟨27274433744859297153145321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36365911659812396204193761 27274433744859297153145321)
  ·
    refine ⟨20455825308644472864858991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27274433744859297153145321 20455825308644472864858991)
    ·
      refine ⟨30683737962966709297288487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20455825308644472864858991 30683737962966709297288487)
      ·
        refine ⟨46025606944450063945932731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30683737962966709297288487 46025606944450063945932731)
        ·
          refine ⟨69038410416675095918899097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46025606944450063945932731 69038410416675095918899097)
          ·
            refine ⟨51778807812506321939174323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69038410416675095918899097 51778807812506321939174323)
            ·
              refine ⟨77668211718759482908761485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51778807812506321939174323 77668211718759482908761485)
              ·
                refine ⟨29125579394534806090785557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77668211718759482908761485 29125579394534806090785557)
                ·
                  refine ⟨1365261534118819035505573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 29125579394534806090785557 1365261534118819035505573)
                  ·
                    refine ⟨255986537647278569157295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1365261534118819035505573 255986537647278569157295)
                    ·
                      rfl

theorem cell23_1495596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 4].length) (baseStart_1495596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1495596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1495596 prefixEnd_1495596 := by exact prefixLift 1495596
  have htrace : WordTrace (prefixWord ++ tailWord_1495596) baseStart_1495596 baseEnd_1495596 := by
    simpa [prefixWord, tailWord_1495596, baseEnd_1495596] using wordTrace_append hprefix tailTrace_1495596
  have hstable : (prefixWord ++ tailWord_1495596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495596).length < 2 ^ (prefixWord ++ tailWord_1495596).sum := by decide
  have hdescent : baseEnd_1495596 < baseStart_1495596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495599 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 6]
def baseStart_1495599 : Nat := 118140960795 + 1495599 * 2 ^ 59
def prefixEnd_1495599 : Nat := 4983230072969 + 3 ^ 40 * 1495599 * 2
def baseEnd_1495599 : Nat := 767961153383799195734371

theorem tailTrace_1495599 : CollatzResearch.WordTrace tailWord_1495599 prefixEnd_1495599 767961153383799195734371 := by
  unfold tailWord_1495599
  simp only [CollatzResearch.WordTrace]
  refine ⟨54548976908707725818649851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36365984605805150545766567 54548976908707725818649851)
  ·
    refine ⟨81823465363061588727974777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54548976908707725818649851 81823465363061588727974777)
    ·
      refine ⟨61367599022296191545981083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81823465363061588727974777 61367599022296191545981083)
      ·
        refine ⟨92051398533444287318971625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61367599022296191545981083 92051398533444287318971625)
        ·
          refine ⟨69038548900083215489228719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92051398533444287318971625 69038548900083215489228719)
          ·
            refine ⟨103557823350124823233843079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69038548900083215489228719 103557823350124823233843079)
            ·
              refine ⟨155336735025187234850764619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103557823350124823233843079 155336735025187234850764619)
              ·
                refine ⟨233005102537780852276146929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155336735025187234850764619 233005102537780852276146929)
                ·
                  refine ⟨174753826903335639207110197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 233005102537780852276146929 174753826903335639207110197)
                  ·
                    refine ⟨16383171272187716175666581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 174753826903335639207110197 16383171272187716175666581)
                    ·
                      refine ⟨767961153383799195734371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16383171272187716175666581 767961153383799195734371)
                      ·
                        rfl

theorem cell23_1495599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 6].length) (baseStart_1495599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1495599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1495599 prefixEnd_1495599 := by exact prefixLift 1495599
  have htrace : WordTrace (prefixWord ++ tailWord_1495599) baseStart_1495599 baseEnd_1495599 := by
    simpa [prefixWord, tailWord_1495599, baseEnd_1495599] using wordTrace_append hprefix tailTrace_1495599
  have hstable : (prefixWord ++ tailWord_1495599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495599).length < 2 ^ (prefixWord ++ tailWord_1495599).sum := by decide
  have hdescent : baseEnd_1495599 < baseStart_1495599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495623 : List Nat := [1, 1, 4, 1, 4, 1, 1, 2, 3, 2, 3]
def baseStart_1495623 : Nat := 118140960795 + 1495623 * 2 ^ 59
def prefixEnd_1495623 : Nat := 4983230072969 + 3 ^ 40 * 1495623 * 2
def baseEnd_1495623 : Nat := 767973476919507101834261

theorem tailTrace_1495623 : CollatzResearch.WordTrace tailWord_1495623 prefixEnd_1495623 767973476919507101834261 := by
  unfold tailWord_1495623
  simp only [CollatzResearch.WordTrace]
  refine ⟨54549852260620777917523523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36366568173747185278349015 54549852260620777917523523)
  ·
    refine ⟨81824778390931166876285285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54549852260620777917523523 81824778390931166876285285)
    ·
      refine ⟨15342145948299593789303491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81824778390931166876285285 15342145948299593789303491)
      ·
        refine ⟨23013218922449390683955237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15342145948299593789303491 23013218922449390683955237)
        ·
          refine ⟨4314978547959260753241607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23013218922449390683955237 4314978547959260753241607)
          ·
            refine ⟨6472467821938891129862411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4314978547959260753241607 6472467821938891129862411)
            ·
              refine ⟨9708701732908336694793617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6472467821938891129862411 9708701732908336694793617)
              ·
                refine ⟨7281526299681252521095213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9708701732908336694793617 7281526299681252521095213)
                ·
                  refine ⟨2730572362380469695410705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7281526299681252521095213 2730572362380469695410705)
                  ·
                    refine ⟨2047929271785352271558029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2730572362380469695410705 2047929271785352271558029)
                    ·
                      refine ⟨767973476919507101834261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2047929271785352271558029 767973476919507101834261)
                      ·
                        rfl

theorem cell23_1495623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 3, 2, 3].length) (baseStart_1495623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1495623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1495623 prefixEnd_1495623 := by exact prefixLift 1495623
  have htrace : WordTrace (prefixWord ++ tailWord_1495623) baseStart_1495623 baseEnd_1495623 := by
    simpa [prefixWord, tailWord_1495623, baseEnd_1495623] using wordTrace_append hprefix tailTrace_1495623
  have hstable : (prefixWord ++ tailWord_1495623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495623).length < 2 ^ (prefixWord ++ tailWord_1495623).sum := by decide
  have hdescent : baseEnd_1495623 < baseStart_1495623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495626 : List Nat := [3, 1, 2, 1, 1, 4, 3, 8]
def baseStart_1495626 : Nat := 118140960795 + 1495626 * 2 ^ 59
def prefixEnd_1495626 : Nat := 4983230072969 + 3 ^ 40 * 1495626 * 2
def baseEnd_1495626 : Nat := 28443519161535947781361

theorem tailTrace_1495626 : CollatzResearch.WordTrace tailWord_1495626 prefixEnd_1495626 28443519161535947781361 := by
  unfold tailWord_1495626
  simp only [CollatzResearch.WordTrace]
  refine ⟨13637490419902477357470683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36366641119739939619921821 13637490419902477357470683)
  ·
    refine ⟨20456235629853716036206025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13637490419902477357470683 20456235629853716036206025)
    ·
      refine ⟨15342176722390287027154519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20456235629853716036206025 15342176722390287027154519)
      ·
        refine ⟨23013265083585430540731779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15342176722390287027154519 23013265083585430540731779)
        ·
          refine ⟨34519897625378145811097669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23013265083585430540731779 34519897625378145811097669)
          ·
            refine ⟨6472480804758402339580813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34519897625378145811097669 6472480804758402339580813)
            ·
              refine ⟨2427180301784400877342805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6472480804758402339580813 2427180301784400877342805)
              ·
                refine ⟨28443519161535947781361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2427180301784400877342805 28443519161535947781361)
                ·
                  rfl

theorem cell23_1495626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 8].length) (baseStart_1495626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1495626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1495626 prefixEnd_1495626 := by exact prefixLift 1495626
  have htrace : WordTrace (prefixWord ++ tailWord_1495626) baseStart_1495626 baseEnd_1495626 := by
    simpa [prefixWord, tailWord_1495626, baseEnd_1495626] using wordTrace_append hprefix tailTrace_1495626
  have hstable : (prefixWord ++ tailWord_1495626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495626).length < 2 ^ (prefixWord ++ tailWord_1495626).sum := by decide
  have hdescent : baseEnd_1495626 < baseStart_1495626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495633 : List Nat := [1, 2, 2, 1, 3, 4, 2, 1, 1, 2, 4]
def baseStart_1495633 : Nat := 118140960795 + 1495633 * 2 ^ 59
def prefixEnd_1495633 : Nat := 4983230072969 + 3 ^ 40 * 1495633 * 2
def baseEnd_1495633 : Nat := 767978611726052062709215

theorem tailTrace_1495633 : CollatzResearch.WordTrace tailWord_1495633 prefixEnd_1495633 767978611726052062709215 := by
  unfold tailWord_1495633
  simp only [CollatzResearch.WordTrace]
  refine ⟨54550216990584549625387553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36366811327056366416925035 54550216990584549625387553)
  ·
    refine ⟨40912662742938412219040665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54550216990584549625387553 40912662742938412219040665)
    ·
      refine ⟨30684497057203809164280499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40912662742938412219040665 30684497057203809164280499)
      ·
        refine ⟨46026745585805713746420749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30684497057203809164280499 46026745585805713746420749)
        ·
          refine ⟨17260029594677142654907781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46026745585805713746420749 17260029594677142654907781)
          ·
            refine ⟨3236255549001964247795209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17260029594677142654907781 3236255549001964247795209)
            ·
              refine ⟨2427191661751473185846407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3236255549001964247795209 2427191661751473185846407)
              ·
                refine ⟨3640787492627209778769611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2427191661751473185846407 3640787492627209778769611)
                ·
                  refine ⟨5461181238940814668154417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3640787492627209778769611 5461181238940814668154417)
                  ·
                    refine ⟨4095885929205611001115813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5461181238940814668154417 4095885929205611001115813)
                    ·
                      refine ⟨767978611726052062709215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4095885929205611001115813 767978611726052062709215)
                      ·
                        rfl

theorem cell23_1495633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 1, 1, 2, 4].length) (baseStart_1495633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1495633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1495633 prefixEnd_1495633 := by exact prefixLift 1495633
  have htrace : WordTrace (prefixWord ++ tailWord_1495633) baseStart_1495633 baseEnd_1495633 := by
    simpa [prefixWord, tailWord_1495633, baseEnd_1495633] using wordTrace_append hprefix tailTrace_1495633
  have hstable : (prefixWord ++ tailWord_1495633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495633).length < 2 ^ (prefixWord ++ tailWord_1495633).sum := by decide
  have hdescent : baseEnd_1495633 < baseStart_1495633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495676 : List Nat := [2, 2, 2, 1, 1, 2, 2, 1, 1, 5, 4]
def baseStart_1495676 : Nat := 118140960795 + 1495676 * 2 ^ 59
def prefixEnd_1495676 : Nat := 4983230072969 + 3 ^ 40 * 1495676 * 2
def baseEnd_1495676 : Nat := 768000691394195394471517

theorem tailTrace_1495676 : CollatzResearch.WordTrace tailWord_1495676 prefixEnd_1495676 768000691394195394471517 := by
  unfold tailWord_1495676
  simp only [CollatzResearch.WordTrace]
  refine ⟨27275892664714383984601441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36367856886285845312801921 27275892664714383984601441)
  ·
    refine ⟨20456919498535787988451081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27275892664714383984601441 20456919498535787988451081)
    ·
      refine ⟨15342689623901840991338311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20456919498535787988451081 15342689623901840991338311)
      ·
        refine ⟨23014034435852761487007467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15342689623901840991338311 23014034435852761487007467)
        ·
          refine ⟨34521051653779142230511201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23014034435852761487007467 34521051653779142230511201)
          ·
            refine ⟨25890788740334356672883401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34521051653779142230511201 25890788740334356672883401)
            ·
              refine ⟨19418091555250767504662551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25890788740334356672883401 19418091555250767504662551)
              ·
                refine ⟨29127137332876151256993827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19418091555250767504662551 29127137332876151256993827)
                ·
                  refine ⟨43690705999314226885490741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29127137332876151256993827 43690705999314226885490741)
                  ·
                    refine ⟨4096003687435708770514757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43690705999314226885490741 4096003687435708770514757)
                    ·
                      refine ⟨768000691394195394471517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4096003687435708770514757 768000691394195394471517)
                      ·
                        rfl

theorem cell23_1495676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_1495676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1495676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1495676 prefixEnd_1495676 := by exact prefixLift 1495676
  have htrace : WordTrace (prefixWord ++ tailWord_1495676) baseStart_1495676 baseEnd_1495676 := by
    simpa [prefixWord, tailWord_1495676, baseEnd_1495676] using wordTrace_append hprefix tailTrace_1495676
  have hstable : (prefixWord ++ tailWord_1495676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495676).length < 2 ^ (prefixWord ++ tailWord_1495676).sum := by decide
  have hdescent : baseEnd_1495676 < baseStart_1495676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495687 : List Nat := [1, 1, 4, 2, 1, 2, 5, 1, 2, 1, 3]
def baseStart_1495687 : Nat := 118140960795 + 1495687 * 2 ^ 59
def prefixEnd_1495687 : Nat := 4983230072969 + 3 ^ 40 * 1495687 * 2
def baseEnd_1495687 : Nat := 768006339681394851433967

theorem tailTrace_1495687 : CollatzResearch.WordTrace tailWord_1495687 prefixEnd_1495687 768006339681394851433967 := by
  unfold tailWord_1495687
  simp only [CollatzResearch.WordTrace]
  refine ⟨54552186532388916847853315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36368124354925944565235543 54552186532388916847853315)
  ·
    refine ⟨81828279798583375271779973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54552186532388916847853315 81828279798583375271779973)
    ·
      refine ⟨15342802462234382863458745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81828279798583375271779973 15342802462234382863458745)
      ·
        refine ⟨11507101846675787147594059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15342802462234382863458745 11507101846675787147594059)
        ·
          refine ⟨17260652770013680721391089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11507101846675787147594059 17260652770013680721391089)
          ·
            refine ⟨12945489577510260541043317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17260652770013680721391089 12945489577510260541043317)
            ·
              refine ⟨1213639647891586925722811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12945489577510260541043317 1213639647891586925722811)
              ·
                refine ⟨1820459471837380388584217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1213639647891586925722811 1820459471837380388584217)
                ·
                  refine ⟨1365344603878035291438163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1820459471837380388584217 1365344603878035291438163)
                  ·
                    refine ⟨2048016905817052937157245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1365344603878035291438163 2048016905817052937157245)
                    ·
                      refine ⟨768006339681394851433967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2048016905817052937157245 768006339681394851433967)
                      ·
                        rfl

theorem cell23_1495687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 5, 1, 2, 1, 3].length) (baseStart_1495687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1495687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1495687 prefixEnd_1495687 := by exact prefixLift 1495687
  have htrace : WordTrace (prefixWord ++ tailWord_1495687) baseStart_1495687 baseEnd_1495687 := by
    simpa [prefixWord, tailWord_1495687, baseEnd_1495687] using wordTrace_append hprefix tailTrace_1495687
  have hstable : (prefixWord ++ tailWord_1495687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495687).length < 2 ^ (prefixWord ++ tailWord_1495687).sum := by decide
  have hdescent : baseEnd_1495687 < baseStart_1495687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495744 : List Nat := [2, 1, 1, 2, 4, 2, 4, 1, 2, 2, 2]
def baseStart_1495744 : Nat := 118140960795 + 1495744 * 2 ^ 59
def prefixEnd_1495744 : Nat := 4983230072969 + 3 ^ 40 * 1495744 * 2
def baseEnd_1495744 : Nat := 768035608078701128421205

theorem tailTrace_1495744 : CollatzResearch.WordTrace tailWord_1495744 prefixEnd_1495744 768035608078701128421205 := by
  unfold tailWord_1495744
  simp only [CollatzResearch.WordTrace]
  refine ⟨27277132746591207791339143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36369510328788277055118857 27277132746591207791339143)
  ·
    refine ⟨40915699119886811687008715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27277132746591207791339143 40915699119886811687008715)
    ·
      refine ⟨61373548679830217530513073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40915699119886811687008715 61373548679830217530513073)
      ·
        refine ⟨46030161509872663147884805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61373548679830217530513073 46030161509872663147884805)
        ·
          refine ⟨8630655283101124340228401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46030161509872663147884805 8630655283101124340228401)
          ·
            refine ⟨6472991462325843255171301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8630655283101124340228401 6472991462325843255171301)
            ·
              refine ⟨1213685899186095610344619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6472991462325843255171301 1213685899186095610344619)
              ·
                refine ⟨1820528848779143415516929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1213685899186095610344619 1820528848779143415516929)
                ·
                  refine ⟨1365396636584357561637697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1820528848779143415516929 1365396636584357561637697)
                  ·
                    refine ⟨1024047477438268171228273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1365396636584357561637697 1024047477438268171228273)
                    ·
                      refine ⟨768035608078701128421205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1024047477438268171228273 768035608078701128421205)
                      ·
                        rfl

theorem cell23_1495744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 4, 1, 2, 2, 2].length) (baseStart_1495744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1495744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1495744 prefixEnd_1495744 := by exact prefixLift 1495744
  have htrace : WordTrace (prefixWord ++ tailWord_1495744) baseStart_1495744 baseEnd_1495744 := by
    simpa [prefixWord, tailWord_1495744, baseEnd_1495744] using wordTrace_append hprefix tailTrace_1495744
  have hstable : (prefixWord ++ tailWord_1495744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495744).length < 2 ^ (prefixWord ++ tailWord_1495744).sum := by decide
  have hdescent : baseEnd_1495744 < baseStart_1495744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495784 : List Nat := [2, 1, 4, 1, 4, 2, 2, 2, 5]
def baseStart_1495784 : Nat := 118140960795 + 1495784 * 2 ^ 59
def prefixEnd_1495784 : Nat := 4983230072969 + 3 ^ 40 * 1495784 * 2
def baseEnd_1495784 : Nat := 85339571922764552435669

theorem tailTrace_1495784 : CollatzResearch.WordTrace tailWord_1495784 prefixEnd_1495784 85339571922764552435669 := by
  unfold tailWord_1495784
  simp only [CollatzResearch.WordTrace]
  refine ⟨27277862206518751207067203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36370482942025001609422937 27277862206518751207067203)
  ·
    refine ⟨40916793309778126810600805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27277862206518751207067203 40916793309778126810600805)
    ·
      refine ⟨7671898745583398776987651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40916793309778126810600805 7671898745583398776987651)
      ·
        refine ⟨11507848118375098165481477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7671898745583398776987651 11507848118375098165481477)
        ·
          refine ⟨2157721522195330906027777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11507848118375098165481477 2157721522195330906027777)
          ·
            refine ⟨1618291141646498179520833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2157721522195330906027777 1618291141646498179520833)
            ·
              refine ⟨1213718356234873634640625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1618291141646498179520833 1213718356234873634640625)
              ·
                refine ⟨910288767176155225980469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1213718356234873634640625 910288767176155225980469)
                ·
                  refine ⟨85339571922764552435669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 910288767176155225980469 85339571922764552435669)
                  ·
                    rfl

theorem cell23_1495784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 2, 2, 5].length) (baseStart_1495784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1495784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1495784 prefixEnd_1495784 := by exact prefixLift 1495784
  have htrace : WordTrace (prefixWord ++ tailWord_1495784) baseStart_1495784 baseEnd_1495784 := by
    simpa [prefixWord, tailWord_1495784, baseEnd_1495784] using wordTrace_append hprefix tailTrace_1495784
  have hstable : (prefixWord ++ tailWord_1495784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495784).length < 2 ^ (prefixWord ++ tailWord_1495784).sum := by decide
  have hdescent : baseEnd_1495784 < baseStart_1495784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495800 : List Nat := [2, 1, 2, 1, 1, 2, 5, 1, 2, 4, 2]
def baseStart_1495800 : Nat := 118140960795 + 1495800 * 2 ^ 59
def prefixEnd_1495800 : Nat := 4983230072969 + 3 ^ 40 * 1495800 * 2
def baseEnd_1495800 : Nat := 768064362995352909320947

theorem tailTrace_1495800 : CollatzResearch.WordTrace tailWord_1495800 prefixEnd_1495800 768064362995352909320947 := by
  unfold tailWord_1495800
  simp only [CollatzResearch.WordTrace]
  refine ⟨27278153990489768573358427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36370871987319691431144569 27278153990489768573358427)
  ·
    refine ⟨40917230985734652860037641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27278153990489768573358427 40917230985734652860037641)
    ·
      refine ⟨30687923239300989645028231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40917230985734652860037641 30687923239300989645028231)
      ·
        refine ⟨46031884858951484467542347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30687923239300989645028231 46031884858951484467542347)
        ·
          refine ⟨69047827288427226701313521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46031884858951484467542347 69047827288427226701313521)
          ·
            refine ⟨51785870466320420025985141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69047827288427226701313521 51785870466320420025985141)
            ·
              refine ⟨4854925356217539377436107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51785870466320420025985141 4854925356217539377436107)
              ·
                refine ⟨7282388034326309066154161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4854925356217539377436107 7282388034326309066154161)
                ·
                  refine ⟨5461791025744731799615621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7282388034326309066154161 5461791025744731799615621)
                  ·
                    refine ⟨1024085817327137212427929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5461791025744731799615621 1024085817327137212427929)
                    ·
                      refine ⟨768064362995352909320947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1024085817327137212427929 768064362995352909320947)
                      ·
                        rfl

theorem cell23_1495800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 2, 4, 2].length) (baseStart_1495800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1495800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1495800 prefixEnd_1495800 := by exact prefixLift 1495800
  have htrace : WordTrace (prefixWord ++ tailWord_1495800) baseStart_1495800 baseEnd_1495800 := by
    simpa [prefixWord, tailWord_1495800, baseEnd_1495800] using wordTrace_append hprefix tailTrace_1495800
  have hstable : (prefixWord ++ tailWord_1495800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495800).length < 2 ^ (prefixWord ++ tailWord_1495800).sum := by decide
  have hdescent : baseEnd_1495800 < baseStart_1495800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495827 : List Nat := [1, 1, 1, 2, 1, 3, 6, 3, 1, 4]
def baseStart_1495827 : Nat := 118140960795 + 1495827 * 2 ^ 59
def prefixEnd_1495827 : Nat := 4983230072969 + 3 ^ 40 * 1495827 * 2
def baseEnd_1495827 : Nat := 256026075657674767894441

theorem tailTrace_1495827 : CollatzResearch.WordTrace tailWord_1495827 prefixEnd_1495827 256026075657674767894441 := by
  unfold tailWord_1495827
  simp only [CollatzResearch.WordTrace]
  refine ⟨54557292751881720757949735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36371528501254480505299823 54557292751881720757949735)
  ·
    refine ⟨81835939127822581136924603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54557292751881720757949735 81835939127822581136924603)
    ·
      refine ⟨122753908691733871705386905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81835939127822581136924603 122753908691733871705386905)
      ·
        refine ⟨92065431518800403779040179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122753908691733871705386905 92065431518800403779040179)
        ·
          refine ⟨138098147278200605668560269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92065431518800403779040179 138098147278200605668560269)
          ·
            refine ⟨51786805229325227125710101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138098147278200605668560269 51786805229325227125710101)
            ·
              refine ⟨2427506495124620021517661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 51786805229325227125710101 2427506495124620021517661)
              ·
                refine ⟨910314935671732508069123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2427506495124620021517661 910314935671732508069123)
                ·
                  refine ⟨1365472403507598762103685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 910314935671732508069123 1365472403507598762103685)
                  ·
                    refine ⟨256026075657674767894441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1365472403507598762103685 256026075657674767894441)
                    ·
                      rfl

theorem cell23_1495827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 3, 1, 4].length) (baseStart_1495827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1495827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1495827 prefixEnd_1495827 := by exact prefixLift 1495827
  have htrace : WordTrace (prefixWord ++ tailWord_1495827) baseStart_1495827 baseEnd_1495827 := by
    simpa [prefixWord, tailWord_1495827, baseEnd_1495827] using wordTrace_append hprefix tailTrace_1495827
  have hstable : (prefixWord ++ tailWord_1495827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495827).length < 2 ^ (prefixWord ++ tailWord_1495827).sum := by decide
  have hdescent : baseEnd_1495827 < baseStart_1495827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495840 : List Nat := [2, 1, 1, 5, 1, 2, 3, 2, 6]
def baseStart_1495840 : Nat := 118140960795 + 1495840 * 2 ^ 59
def prefixEnd_1495840 : Nat := 4983230072969 + 3 ^ 40 * 1495840 * 2
def baseEnd_1495840 : Nat := 85342766913503639202307

theorem tailTrace_1495840 : CollatzResearch.WordTrace tailWord_1495840 prefixEnd_1495840 85342766913503639202307 := by
  unfold tailWord_1495840
  simp only [CollatzResearch.WordTrace]
  refine ⟨27278883450417311989086487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36371844600556415985448649 27278883450417311989086487)
  ·
    refine ⟨40918325175625967983629731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27278883450417311989086487 40918325175625967983629731)
    ·
      refine ⟨61377487763438951975444597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40918325175625967983629731 61377487763438951975444597)
      ·
        refine ⟨5754139477822401747697931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61377487763438951975444597 5754139477822401747697931)
        ·
          refine ⟨8631209216733602621546897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5754139477822401747697931 8631209216733602621546897)
          ·
            refine ⟨6473406912550201966160173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8631209216733602621546897 6473406912550201966160173)
            ·
              refine ⟨2427527592206325737310065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6473406912550201966160173 2427527592206325737310065)
              ·
                refine ⟨1820645694154744302982549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2427527592206325737310065 1820645694154744302982549)
                ·
                  refine ⟨85342766913503639202307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1820645694154744302982549 85342766913503639202307)
                  ·
                    rfl

theorem cell23_1495840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 2, 6].length) (baseStart_1495840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1495840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1495840 prefixEnd_1495840 := by exact prefixLift 1495840
  have htrace : WordTrace (prefixWord ++ tailWord_1495840) baseStart_1495840 baseEnd_1495840 := by
    simpa [prefixWord, tailWord_1495840, baseEnd_1495840] using wordTrace_append hprefix tailTrace_1495840
  have hstable : (prefixWord ++ tailWord_1495840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495840).length < 2 ^ (prefixWord ++ tailWord_1495840).sum := by decide
  have hdescent : baseEnd_1495840 < baseStart_1495840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495903 : List Nat := [1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 6]
def baseStart_1495903 : Nat := 118140960795 + 1495903 * 2 ^ 59
def prefixEnd_1495903 : Nat := 4983230072969 + 3 ^ 40 * 1495903 * 2
def baseEnd_1495903 : Nat := 768117251502766006332973

theorem tailTrace_1495903 : CollatzResearch.WordTrace tailWord_1495903 prefixEnd_1495903 768117251502766006332973 := by
  unfold tailWord_1495903
  simp only [CollatzResearch.WordTrace]
  refine ⟨54560064699606385737716363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36373376466404257158477575 54560064699606385737716363)
  ·
    refine ⟨81840097049409578606574545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54560064699606385737716363 81840097049409578606574545)
    ·
      refine ⟨61380072787057183954930909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81840097049409578606574545 61380072787057183954930909)
      ·
        refine ⟨23017527295146443983099091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61380072787057183954930909 23017527295146443983099091)
        ·
          refine ⟨34526290942719665974648637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23017527295146443983099091 34526290942719665974648637)
          ·
            refine ⟨12947359103519874740493239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34526290942719665974648637 12947359103519874740493239)
            ·
              refine ⟨19421038655279812110739859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12947359103519874740493239 19421038655279812110739859)
              ·
                refine ⟨29131557982919718166109789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19421038655279812110739859 29131557982919718166109789)
                ·
                  refine ⟨10924334243594894312291171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29131557982919718166109789 10924334243594894312291171)
                  ·
                    refine ⟨16386501365392341468436757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10924334243594894312291171 16386501365392341468436757)
                    ·
                      refine ⟨768117251502766006332973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16386501365392341468436757 768117251502766006332973)
                      ·
                        rfl

theorem cell23_1495903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_1495903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1495903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1495903 prefixEnd_1495903 := by exact prefixLift 1495903
  have htrace : WordTrace (prefixWord ++ tailWord_1495903) baseStart_1495903 baseEnd_1495903 := by
    simpa [prefixWord, tailWord_1495903, baseEnd_1495903] using wordTrace_append hprefix tailTrace_1495903
  have hstable : (prefixWord ++ tailWord_1495903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495903).length < 2 ^ (prefixWord ++ tailWord_1495903).sum := by decide
  have hdescent : baseEnd_1495903 < baseStart_1495903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495934 : List Nat := [4, 2, 3, 1, 2, 1, 1, 2, 1, 6]
def baseStart_1495934 : Nat := 118140960795 + 1495934 * 2 ^ 59
def prefixEnd_1495934 : Nat := 4983230072969 + 3 ^ 40 * 1495934 * 2
def baseEnd_1495934 : Nat := 256044389801018461681777

theorem tailTrace_1495934 : CollatzResearch.WordTrace tailWord_1495934 prefixEnd_1495934 256044389801018461681777 := by
  unfold tailWord_1495934
  simp only [CollatzResearch.WordTrace]
  refine ⟨6820149420311759754011857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36374130241662718688063237 6820149420311759754011857)
  ·
    refine ⟨5115112065233819815508893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6820149420311759754011857 5115112065233819815508893)
    ·
      refine ⟨1918167024462682430815835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5115112065233819815508893 1918167024462682430815835)
      ·
        refine ⟨2877250536694023646223753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1918167024462682430815835 2877250536694023646223753)
        ·
          refine ⟨2157937902520517734667815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2877250536694023646223753 2157937902520517734667815)
          ·
            refine ⟨3236906853780776602001723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2157937902520517734667815 3236906853780776602001723)
            ·
              refine ⟨4855360280671164903002585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3236906853780776602001723 4855360280671164903002585)
              ·
                refine ⟨3641520210503373677251939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4855360280671164903002585 3641520210503373677251939)
                ·
                  refine ⟨5462280315755060515877909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3641520210503373677251939 5462280315755060515877909)
                  ·
                    refine ⟨256044389801018461681777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5462280315755060515877909 256044389801018461681777)
                    ·
                      rfl

theorem cell23_1495934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_1495934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1495934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1495934 prefixEnd_1495934 := by exact prefixLift 1495934
  have htrace : WordTrace (prefixWord ++ tailWord_1495934) baseStart_1495934 baseEnd_1495934 := by
    simpa [prefixWord, tailWord_1495934, baseEnd_1495934] using wordTrace_append hprefix tailTrace_1495934
  have hstable : (prefixWord ++ tailWord_1495934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495934).length < 2 ^ (prefixWord ++ tailWord_1495934).sum := by decide
  have hdescent : baseEnd_1495934 < baseStart_1495934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495938 : List Nat := [3, 4, 2, 2, 1, 1, 3, 1, 1, 5]
def baseStart_1495938 : Nat := 118140960795 + 1495938 * 2 ^ 59
def prefixEnd_1495938 : Nat := 4983230072969 + 3 ^ 40 * 1495938 * 2
def baseEnd_1495938 : Nat := 256045074441891123131771

theorem tailTrace_1495938 : CollatzResearch.WordTrace tailWord_1495938 prefixEnd_1495938 256045074441891123131771 := by
  unfold tailWord_1495938
  simp only [CollatzResearch.WordTrace]
  refine ⟨13640335313619896678810117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36374227502986391143493645 13640335313619896678810117)
  ·
    refine ⟨2557562871303730627276897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13640335313619896678810117 2557562871303730627276897)
    ·
      refine ⟨1918172153477797970457673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2557562871303730627276897 1918172153477797970457673)
      ·
        refine ⟨1438629115108348477843255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1918172153477797970457673 1438629115108348477843255)
        ·
          refine ⟨2157943672662522716764883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1438629115108348477843255 2157943672662522716764883)
          ·
            refine ⟨3236915508993784075147325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2157943672662522716764883 3236915508993784075147325)
            ·
              refine ⟨1213843315872669028180247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3236915508993784075147325 1213843315872669028180247)
              ·
                refine ⟨1820764973809003542270371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1213843315872669028180247 1820764973809003542270371)
                ·
                  refine ⟨2731147460713505313405557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1820764973809003542270371 2731147460713505313405557)
                  ·
                    refine ⟨256045074441891123131771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2731147460713505313405557 256045074441891123131771)
                    ·
                      rfl

theorem cell23_1495938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_1495938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1495938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1495938 prefixEnd_1495938 := by exact prefixLift 1495938
  have htrace : WordTrace (prefixWord ++ tailWord_1495938) baseStart_1495938 baseEnd_1495938 := by
    simpa [prefixWord, tailWord_1495938, baseEnd_1495938] using wordTrace_append hprefix tailTrace_1495938
  have hstable : (prefixWord ++ tailWord_1495938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495938).length < 2 ^ (prefixWord ++ tailWord_1495938).sum := by decide
  have hdescent : baseEnd_1495938 < baseStart_1495938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1495964 : List Nat := [2, 2, 3, 3, 3, 1, 1, 8]
def baseStart_1495964 : Nat := 118140960795 + 1495964 * 2 ^ 59
def prefixEnd_1495964 : Nat := 4983230072969 + 3 ^ 40 * 1495964 * 2
def baseEnd_1495964 : Nat := 28449947178618158061859

theorem tailTrace_1495964 : CollatzResearch.WordTrace tailWord_1495964 prefixEnd_1495964 28449947178618158061859 := by
  unfold tailWord_1495964
  simp only [CollatzResearch.WordTrace]
  refine ⟨27281144776192696577843473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36374859701590262103791297 27281144776192696577843473)
  ·
    refine ⟨20460858582144522433382605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27281144776192696577843473 20460858582144522433382605)
    ·
      refine ⟨7672821968304195912518477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20460858582144522433382605 7672821968304195912518477)
      ·
        refine ⟨2877308238114073467194429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7672821968304195912518477 2877308238114073467194429)
        ·
          refine ⟨1078990589292777550197911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2877308238114073467194429 1078990589292777550197911)
          ·
            refine ⟨1618485883939166325296867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1078990589292777550197911 1618485883939166325296867)
            ·
              refine ⟨2427728825908749487945301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1618485883939166325296867 2427728825908749487945301)
              ·
                refine ⟨28449947178618158061859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2427728825908749487945301 28449947178618158061859)
                ·
                  rfl

theorem cell23_1495964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 8].length) (baseStart_1495964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1495964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1495964 prefixEnd_1495964 := by exact prefixLift 1495964
  have htrace : WordTrace (prefixWord ++ tailWord_1495964) baseStart_1495964 baseEnd_1495964 := by
    simpa [prefixWord, tailWord_1495964, baseEnd_1495964] using wordTrace_append hprefix tailTrace_1495964
  have hstable : (prefixWord ++ tailWord_1495964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1495964).length < 2 ^ (prefixWord ++ tailWord_1495964).sum := by decide
  have hdescent : baseEnd_1495964 < baseStart_1495964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1495964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496008 : List Nat := [2, 1, 3, 1, 6, 1, 1, 2, 2, 1, 3]
def baseStart_1496008 : Nat := 118140960795 + 1496008 * 2 ^ 59
def prefixEnd_1496008 : Nat := 4983230072969 + 3 ^ 40 * 1496008 * 2
def baseEnd_1496008 : Nat := 768171166971488095519991

theorem tailTrace_1496008 : CollatzResearch.WordTrace tailWord_1496008 prefixEnd_1496008 768171166971488095519991 := by
  unfold tailWord_1496008
  simp only [CollatzResearch.WordTrace]
  refine ⟨27281947182112994335144339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36375929576150659113525785 27281947182112994335144339)
  ·
    refine ⟨40922920773169491502716509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27281947182112994335144339 40922920773169491502716509)
    ·
      refine ⟨15346095289938559313518691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40922920773169491502716509 15346095289938559313518691)
      ·
        refine ⟨23019142934907838970278037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15346095289938559313518691 23019142934907838970278037)
        ·
          refine ⟨1079022325073804951731783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 23019142934907838970278037 1079022325073804951731783)
          ·
            refine ⟨1618533487610707427597675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1079022325073804951731783 1618533487610707427597675)
            ·
              refine ⟨2427800231416061141396513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1618533487610707427597675 2427800231416061141396513)
              ·
                refine ⟨1820850173562045856047385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2427800231416061141396513 1820850173562045856047385)
                ·
                  refine ⟨1365637630171534392035539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1820850173562045856047385 1365637630171534392035539)
                  ·
                    refine ⟨2048456445257301588053309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1365637630171534392035539 2048456445257301588053309)
                    ·
                      refine ⟨768171166971488095519991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2048456445257301588053309 768171166971488095519991)
                      ·
                        rfl

theorem cell23_1496008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 2, 2, 1, 3].length) (baseStart_1496008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1496008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1496008 prefixEnd_1496008 := by exact prefixLift 1496008
  have htrace : WordTrace (prefixWord ++ tailWord_1496008) baseStart_1496008 baseEnd_1496008 := by
    simpa [prefixWord, tailWord_1496008, baseEnd_1496008] using wordTrace_append hprefix tailTrace_1496008
  have hstable : (prefixWord ++ tailWord_1496008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496008).length < 2 ^ (prefixWord ++ tailWord_1496008).sum := by decide
  have hdescent : baseEnd_1496008 < baseStart_1496008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496031 : List Nat := [1, 1, 2, 3, 5, 2, 1, 1, 1, 4, 2]
def baseStart_1496031 : Nat := 118140960795 + 1496031 * 2 ^ 59
def prefixEnd_1496031 : Nat := 4983230072969 + 3 ^ 40 * 1496031 * 2
def baseEnd_1496031 : Nat := 768182977026541505532385

theorem tailTrace_1496031 : CollatzResearch.WordTrace tailWord_1496031 prefixEnd_1496031 768182977026541505532385 := by
  unfold tailWord_1496031
  simp only [CollatzResearch.WordTrace]
  refine ⟨54564733243142663598375947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36376488828761775732250631 54564733243142663598375947)
  ·
    refine ⟨81847099864713995397563921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54564733243142663598375947 81847099864713995397563921)
    ·
      refine ⟨61385324898535496548172941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81847099864713995397563921 61385324898535496548172941)
      ·
        refine ⟨23019496836950811205564853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61385324898535496548172941 23019496836950811205564853)
        ·
          refine ⟨2158077828464138550521705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23019496836950811205564853 2158077828464138550521705)
          ·
            refine ⟨1618558371348103912891279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2158077828464138550521705 1618558371348103912891279)
            ·
              refine ⟨2427837557022155869336919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1618558371348103912891279 2427837557022155869336919)
              ·
                refine ⟨3641756335533233804005379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2427837557022155869336919 3641756335533233804005379)
                ·
                  refine ⟨5462634503299850706008069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3641756335533233804005379 5462634503299850706008069)
                  ·
                    refine ⟨1024243969368722007376513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5462634503299850706008069 1024243969368722007376513)
                    ·
                      refine ⟨768182977026541505532385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1024243969368722007376513 768182977026541505532385)
                      ·
                        rfl

theorem cell23_1496031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 1, 1, 4, 2].length) (baseStart_1496031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1496031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1496031 prefixEnd_1496031 := by exact prefixLift 1496031
  have htrace : WordTrace (prefixWord ++ tailWord_1496031) baseStart_1496031 baseEnd_1496031 := by
    simpa [prefixWord, tailWord_1496031, baseEnd_1496031] using wordTrace_append hprefix tailTrace_1496031
  have hstable : (prefixWord ++ tailWord_1496031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496031).length < 2 ^ (prefixWord ++ tailWord_1496031).sum := by decide
  have hdescent : baseEnd_1496031 < baseStart_1496031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496082 : List Nat := [3, 2, 5, 1, 1, 1, 1, 3, 2, 2, 2]
def baseStart_1496082 : Nat := 118140960795 + 1496082 * 2 ^ 59
def prefixEnd_1496082 : Nat := 4983230072969 + 3 ^ 40 * 1496082 * 2
def baseEnd_1496082 : Nat := 768209164539920805994651

theorem tailTrace_1496082 : CollatzResearch.WordTrace tailWord_1496082 prefixEnd_1496082 768209164539920805994651 := by
  unfold tailWord_1496082
  simp only [CollatzResearch.WordTrace]
  refine ⟨13641648341489474827120625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36377728910638599538988333 13641648341489474827120625)
  ·
    refine ⟨10231236256117106120340469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13641648341489474827120625 10231236256117106120340469)
    ·
      refine ⟨959178399010978698781919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10231236256117106120340469 959178399010978698781919)
      ·
        refine ⟨1438767598516468048172879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 959178399010978698781919 1438767598516468048172879)
        ·
          refine ⟨2158151397774702072259319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1438767598516468048172879 2158151397774702072259319)
          ·
            refine ⟨3237227096662053108388979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2158151397774702072259319 3237227096662053108388979)
            ·
              refine ⟨4855840644993079662583469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3237227096662053108388979 4855840644993079662583469)
              ·
                refine ⟨1820940241872404873468801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4855840644993079662583469 1820940241872404873468801)
                ·
                  refine ⟨1365705181404303655101601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1820940241872404873468801 1365705181404303655101601)
                  ·
                    refine ⟨1024278886053227741326201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1365705181404303655101601 1024278886053227741326201)
                    ·
                      refine ⟨768209164539920805994651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1024278886053227741326201 768209164539920805994651)
                      ·
                        rfl

theorem cell23_1496082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_1496082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1496082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1496082 prefixEnd_1496082 := by exact prefixLift 1496082
  have htrace : WordTrace (prefixWord ++ tailWord_1496082) baseStart_1496082 baseEnd_1496082 := by
    simpa [prefixWord, tailWord_1496082, baseEnd_1496082] using wordTrace_append hprefix tailTrace_1496082
  have hstable : (prefixWord ++ tailWord_1496082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496082).length < 2 ^ (prefixWord ++ tailWord_1496082).sum := by decide
  have hdescent : baseEnd_1496082 < baseStart_1496082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496124 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3]
def baseStart_1496124 : Nat := 118140960795 + 1496124 * 2 ^ 59
def prefixEnd_1496124 : Nat := 4983230072969 + 3 ^ 40 * 1496124 * 2
def baseEnd_1496124 : Nat := 768230730727409641669457

theorem tailTrace_1496124 : CollatzResearch.WordTrace tailWord_1496124 prefixEnd_1496124 768230730727409641669457 := by
  unfold tailWord_1496124
  simp only [CollatzResearch.WordTrace]
  refine ⟨27284062615902870240755713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36378750154537160321007617 27284062615902870240755713)
  ·
    refine ⟨20463046961927152680566785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27284062615902870240755713 20463046961927152680566785)
    ·
      refine ⟨15347285221445364510425089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20463046961927152680566785 15347285221445364510425089)
      ·
        refine ⟨11510463916084023382818817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15347285221445364510425089 11510463916084023382818817)
        ·
          refine ⟨8632847937063017537114113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11510463916084023382818817 8632847937063017537114113)
          ·
            refine ⟨6474635952797263152835585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8632847937063017537114113 6474635952797263152835585)
            ·
              refine ⟨4855976964597947364626689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6474635952797263152835585 4855976964597947364626689)
              ·
                refine ⟨3641982723448460523470017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4855976964597947364626689 3641982723448460523470017)
                ·
                  refine ⟨2731487042586345392602513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3641982723448460523470017 2731487042586345392602513)
                  ·
                    refine ⟨2048615281939759044451885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2731487042586345392602513 2048615281939759044451885)
                    ·
                      refine ⟨768230730727409641669457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2048615281939759044451885 768230730727409641669457)
                      ·
                        rfl

theorem cell23_1496124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3].length) (baseStart_1496124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1496124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1496124 prefixEnd_1496124 := by exact prefixLift 1496124
  have htrace : WordTrace (prefixWord ++ tailWord_1496124) baseStart_1496124 baseEnd_1496124 := by
    simpa [prefixWord, tailWord_1496124, baseEnd_1496124] using wordTrace_append hprefix tailTrace_1496124
  have hstable : (prefixWord ++ tailWord_1496124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496124).length < 2 ^ (prefixWord ++ tailWord_1496124).sum := by decide
  have hdescent : baseEnd_1496124 < baseStart_1496124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496158 : List Nat := [4, 4, 1, 1, 1, 2, 1, 1, 1, 4, 3]
def baseStart_1496158 : Nat := 118140960795 + 1496158 * 2 ^ 59
def prefixEnd_1496158 : Nat := 4983230072969 + 3 ^ 40 * 1496158 * 2
def baseEnd_1496158 : Nat := 768248189069662508644301

theorem tailTrace_1496158 : CollatzResearch.WordTrace tailWord_1496158 prefixEnd_1496158 768248189069662508644301 := by
  unfold tailWord_1496158
  simp only [CollatzResearch.WordTrace]
  refine ⟨6821170664210320536031141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36379576875788376192166085 6821170664210320536031141)
  ·
    refine ⟨1278969499539435100505839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6821170664210320536031141 1278969499539435100505839)
    ·
      refine ⟨1918454249309152650758759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1278969499539435100505839 1918454249309152650758759)
      ·
        refine ⟨2877681373963728976138139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1918454249309152650758759 2877681373963728976138139)
        ·
          refine ⟨4316522060945593464207209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2877681373963728976138139 4316522060945593464207209)
          ·
            refine ⟨3237391545709195098155407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4316522060945593464207209 3237391545709195098155407)
            ·
              refine ⟨4856087318563792647233111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3237391545709195098155407 4856087318563792647233111)
              ·
                refine ⟨7284130977845688970849667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4856087318563792647233111 7284130977845688970849667)
                ·
                  refine ⟨10926196466768533456274501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7284130977845688970849667 10926196466768533456274501)
                  ·
                    refine ⟨2048661837519100023051469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10926196466768533456274501 2048661837519100023051469)
                    ·
                      refine ⟨768248189069662508644301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2048661837519100023051469 768248189069662508644301)
                      ·
                        rfl

theorem cell23_1496158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_1496158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1496158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1496158 prefixEnd_1496158 := by exact prefixLift 1496158
  have htrace : WordTrace (prefixWord ++ tailWord_1496158) baseStart_1496158 baseEnd_1496158 := by
    simpa [prefixWord, tailWord_1496158, baseEnd_1496158] using wordTrace_append hprefix tailTrace_1496158
  have hstable : (prefixWord ++ tailWord_1496158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496158).length < 2 ^ (prefixWord ++ tailWord_1496158).sum := by decide
  have hdescent : baseEnd_1496158 < baseStart_1496158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496177 : List Nat := [1, 2, 2, 2, 1, 1, 2, 2, 5, 1, 4]
def baseStart_1496177 : Nat := 118140960795 + 1496177 * 2 ^ 59
def prefixEnd_1496177 : Nat := 4983230072969 + 3 ^ 40 * 1496177 * 2
def baseEnd_1496177 : Nat := 768257945202097934306713

theorem tailTrace_1496177 : CollatzResearch.WordTrace tailWord_1496177 prefixEnd_1496177 768257945202097934306713 := by
  unfold tailWord_1496177
  simp only [CollatzResearch.WordTrace]
  refine ⟨54570058300613730533190785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36380038867075820355460523 54570058300613730533190785)
  ·
    refine ⟨40927543725460297899893089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54570058300613730533190785 40927543725460297899893089)
    ·
      refine ⟨30695657794095223424919817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40927543725460297899893089 30695657794095223424919817)
      ·
        refine ⟨23021743345571417568689863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30695657794095223424919817 23021743345571417568689863)
        ·
          refine ⟨34532615018357126353034795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23021743345571417568689863 34532615018357126353034795)
          ·
            refine ⟨51798922527535689529552193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34532615018357126353034795 51798922527535689529552193)
            ·
              refine ⟨38849191895651767147164145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51798922527535689529552193 38849191895651767147164145)
              ·
                refine ⟨29136893921738825360373109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38849191895651767147164145 29136893921738825360373109)
                ·
                  refine ⟨2731583805163014877534979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29136893921738825360373109 2731583805163014877534979)
                  ·
                    refine ⟨4097375707744522316302469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2731583805163014877534979 4097375707744522316302469)
                    ·
                      refine ⟨768257945202097934306713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4097375707744522316302469 768257945202097934306713)
                      ·
                        rfl

theorem cell23_1496177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 5, 1, 4].length) (baseStart_1496177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1496177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1496177 prefixEnd_1496177 := by exact prefixLift 1496177
  have htrace : WordTrace (prefixWord ++ tailWord_1496177) baseStart_1496177 baseEnd_1496177 := by
    simpa [prefixWord, tailWord_1496177, baseEnd_1496177] using wordTrace_append hprefix tailTrace_1496177
  have hstable : (prefixWord ++ tailWord_1496177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496177).length < 2 ^ (prefixWord ++ tailWord_1496177).sum := by decide
  have hdescent : baseEnd_1496177 < baseStart_1496177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496204 : List Nat := [2, 2, 1, 2, 1, 1, 1, 7, 2, 4]
def baseStart_1496204 : Nat := 118140960795 + 1496204 * 2 ^ 59
def prefixEnd_1496204 : Nat := 4983230072969 + 3 ^ 40 * 1496204 * 2
def baseEnd_1496204 : Nat := 256090603059923109556363

theorem tailTrace_1496204 : CollatzResearch.WordTrace tailWord_1496204 prefixEnd_1496204 256090603059923109556363 := by
  unfold tailWord_1496204
  simp only [CollatzResearch.WordTrace]
  refine ⟨27285521535757957072211833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36380695381010609429615777 27285521535757957072211833)
  ·
    refine ⟨20464141151818467804158875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27285521535757957072211833 20464141151818467804158875)
    ·
      refine ⟨30696211727727701706238313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20464141151818467804158875 30696211727727701706238313)
      ·
        refine ⟨23022158795795776279678735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30696211727727701706238313 23022158795795776279678735)
        ·
          refine ⟨34533238193693664419518103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23022158795795776279678735 34533238193693664419518103)
          ·
            refine ⟨51799857290540496629277155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34533238193693664419518103 51799857290540496629277155)
            ·
              refine ⟨77699785935810744943915733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51799857290540496629277155 77699785935810744943915733)
              ·
                refine ⟨1821088732870564334623025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 77699785935810744943915733 1821088732870564334623025)
                ·
                  refine ⟨1365816549652923250967269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1821088732870564334623025 1365816549652923250967269)
                  ·
                    refine ⟨256090603059923109556363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1365816549652923250967269 256090603059923109556363)
                    ·
                      rfl

theorem cell23_1496204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 7, 2, 4].length) (baseStart_1496204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1496204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1496204 prefixEnd_1496204 := by exact prefixLift 1496204
  have htrace : WordTrace (prefixWord ++ tailWord_1496204) baseStart_1496204 baseEnd_1496204 := by
    simpa [prefixWord, tailWord_1496204, baseEnd_1496204] using wordTrace_append hprefix tailTrace_1496204
  have hstable : (prefixWord ++ tailWord_1496204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496204).length < 2 ^ (prefixWord ++ tailWord_1496204).sum := by decide
  have hdescent : baseEnd_1496204 < baseStart_1496204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496211 : List Nat := [1, 1, 1, 2, 1, 2, 6, 2, 3, 2, 2]
def baseStart_1496211 : Nat := 118140960795 + 1496211 * 2 ^ 59
def prefixEnd_1496211 : Nat := 4983230072969 + 3 ^ 40 * 1496211 * 2
def baseEnd_1496211 : Nat := 768275403544350801281557

theorem tailTrace_1496211 : CollatzResearch.WordTrace tailWord_1496211 prefixEnd_1496211 768275403544350801281557 := by
  unfold tailWord_1496211
  simp only [CollatzResearch.WordTrace]
  refine ⟨54571298382490554339928487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36380865588327036226618991 54571298382490554339928487)
  ·
    refine ⟨81856947573735831509892731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54571298382490554339928487 81856947573735831509892731)
    ·
      refine ⟨122785421360603747264839097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81856947573735831509892731 122785421360603747264839097)
      ·
        refine ⟨92089066020452810448629323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122785421360603747264839097 92089066020452810448629323)
        ·
          refine ⟨138133599030679215672943985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92089066020452810448629323 138133599030679215672943985)
          ·
            refine ⟨103600199273009411754707989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138133599030679215672943985 103600199273009411754707989)
            ·
              refine ⟨4856259340922316176001937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 103600199273009411754707989 4856259340922316176001937)
              ·
                refine ⟨3642194505691737132001453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4856259340922316176001937 3642194505691737132001453)
                ·
                  refine ⟨1365822939634401424500545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3642194505691737132001453 1365822939634401424500545)
                  ·
                    refine ⟨1024367204725801068375409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1365822939634401424500545 1024367204725801068375409)
                    ·
                      refine ⟨768275403544350801281557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1024367204725801068375409 768275403544350801281557)
                      ·
                        rfl

theorem cell23_1496211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 2, 3, 2, 2].length) (baseStart_1496211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1496211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1496211 prefixEnd_1496211 := by exact prefixLift 1496211
  have htrace : WordTrace (prefixWord ++ tailWord_1496211) baseStart_1496211 baseEnd_1496211 := by
    simpa [prefixWord, tailWord_1496211, baseEnd_1496211] using wordTrace_append hprefix tailTrace_1496211
  have hstable : (prefixWord ++ tailWord_1496211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496211).length < 2 ^ (prefixWord ++ tailWord_1496211).sum := by decide
  have hdescent : baseEnd_1496211 < baseStart_1496211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496222 : List Nat := [4, 3, 1, 1, 2, 3, 1, 3, 1, 1, 3]
def baseStart_1496222 : Nat := 118140960795 + 1496222 * 2 ^ 59
def prefixEnd_1496222 : Nat := 4983230072969 + 3 ^ 40 * 1496222 * 2
def baseEnd_1496222 : Nat := 768281051831550258244007

theorem tailTrace_1496222 : CollatzResearch.WordTrace tailWord_1496222 prefixEnd_1496222 768281051831550258244007 := by
  unfold tailWord_1496222
  simp only [CollatzResearch.WordTrace]
  refine ⟨6821462448181337902322365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36381133056967135479052613 6821462448181337902322365)
  ·
    refine ⟨2558048418068001713370887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6821462448181337902322365 2558048418068001713370887)
    ·
      refine ⟨3837072627102002570056331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2558048418068001713370887 3837072627102002570056331)
      ·
        refine ⟨5755608940653003855084497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3837072627102002570056331 5755608940653003855084497)
        ·
          refine ⟨4316706705489752891313373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5755608940653003855084497 4316706705489752891313373)
          ·
            refine ⟨1618765014558657334242515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4316706705489752891313373 1618765014558657334242515)
            ·
              refine ⟨2428147521837986001363773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1618765014558657334242515 2428147521837986001363773)
              ·
                refine ⟨910555320689244750511415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2428147521837986001363773 910555320689244750511415)
                ·
                  refine ⟨1365832981033867125767123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 910555320689244750511415 1365832981033867125767123)
                  ·
                    refine ⟨2048749471550800688650685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1365832981033867125767123 2048749471550800688650685)
                    ·
                      refine ⟨768281051831550258244007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2048749471550800688650685 768281051831550258244007)
                      ·
                        rfl

theorem cell23_1496222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 3, 1, 1, 3].length) (baseStart_1496222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1496222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1496222 prefixEnd_1496222 := by exact prefixLift 1496222
  have htrace : WordTrace (prefixWord ++ tailWord_1496222) baseStart_1496222 baseEnd_1496222 := by
    simpa [prefixWord, tailWord_1496222, baseEnd_1496222] using wordTrace_append hprefix tailTrace_1496222
  have hstable : (prefixWord ++ tailWord_1496222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496222).length < 2 ^ (prefixWord ++ tailWord_1496222).sum := by decide
  have hdescent : baseEnd_1496222 < baseStart_1496222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496231 : List Nat := [1, 1, 6, 2, 1, 2, 2, 1, 1, 1, 5]
def baseStart_1496231 : Nat := 118140960795 + 1496231 * 2 ^ 59
def prefixEnd_1496231 : Nat := 4983230072969 + 3 ^ 40 * 1496231 * 2
def baseEnd_1496231 : Nat := 768285673157440723031465

theorem tailTrace_1496231 : CollatzResearch.WordTrace tailWord_1496231 prefixEnd_1496231 768285673157440723031465 := by
  unfold tailWord_1496231
  simp only [CollatzResearch.WordTrace]
  refine ⟨54572027842418097755656547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36381351894945398503771031 54572027842418097755656547)
  ·
    refine ⟨81858041763627146633484821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54572027842418097755656547 81858041763627146633484821)
    ·
      refine ⟨3837095707670022498444601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 81858041763627146633484821 3837095707670022498444601)
      ·
        refine ⟨2877821780752516873833451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3837095707670022498444601 2877821780752516873833451)
        ·
          refine ⟨4316732671128775310750177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2877821780752516873833451 4316732671128775310750177)
          ·
            refine ⟨3237549503346581483062633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4316732671128775310750177 3237549503346581483062633)
            ·
              refine ⟨2428162127509936112296975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3237549503346581483062633 2428162127509936112296975)
              ·
                refine ⟨3642243191264904168445463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2428162127509936112296975 3642243191264904168445463)
                ·
                  refine ⟨5463364786897356252668195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3642243191264904168445463 5463364786897356252668195)
                  ·
                    refine ⟨8195047180346034379002293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5463364786897356252668195 8195047180346034379002293)
                    ·
                      refine ⟨768285673157440723031465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8195047180346034379002293 768285673157440723031465)
                      ·
                        rfl

theorem cell23_1496231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_1496231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1496231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1496231 prefixEnd_1496231 := by exact prefixLift 1496231
  have htrace : WordTrace (prefixWord ++ tailWord_1496231) baseStart_1496231 baseEnd_1496231 := by
    simpa [prefixWord, tailWord_1496231, baseEnd_1496231] using wordTrace_append hprefix tailTrace_1496231
  have hstable : (prefixWord ++ tailWord_1496231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496231).length < 2 ^ (prefixWord ++ tailWord_1496231).sum := by decide
  have hdescent : baseEnd_1496231 < baseStart_1496231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496234 : List Nat := [3, 1, 5, 1, 1, 1, 11]
def baseStart_1496234 : Nat := 118140960795 + 1496234 * 2 ^ 59
def prefixEnd_1496234 : Nat := 4983230072969 + 3 ^ 40 * 1496234 * 2
def baseEnd_1496234 : Nat := 9485027328387706312271

theorem tailTrace_1496234 : CollatzResearch.WordTrace tailWord_1496234 prefixEnd_1496234 9485027328387706312271 := by
  unfold tailWord_1496234
  simp only [CollatzResearch.WordTrace]
  refine ⟨13643034315351807317003939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36381424840938152845343837 13643034315351807317003939)
  ·
    refine ⟨20464551473027710975505909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13643034315351807317003939 20464551473027710975505909)
    ·
      refine ⟨1918551700596347903953679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20464551473027710975505909 1918551700596347903953679)
      ·
        refine ⟨2877827550894521855930519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1918551700596347903953679 2877827550894521855930519)
        ·
          refine ⟨4316741326341782783895779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2877827550894521855930519 4316741326341782783895779)
          ·
            refine ⟨6475111989512674175843669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4316741326341782783895779 6475111989512674175843669)
            ·
              refine ⟨9485027328387706312271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 6475111989512674175843669 9485027328387706312271)
              ·
                rfl

theorem cell23_1496234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 11].length) (baseStart_1496234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1496234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1496234 prefixEnd_1496234 := by exact prefixLift 1496234
  have htrace : WordTrace (prefixWord ++ tailWord_1496234) baseStart_1496234 baseEnd_1496234 := by
    simpa [prefixWord, tailWord_1496234, baseEnd_1496234] using wordTrace_append hprefix tailTrace_1496234
  have hstable : (prefixWord ++ tailWord_1496234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496234).length < 2 ^ (prefixWord ++ tailWord_1496234).sum := by decide
  have hdescent : baseEnd_1496234 < baseStart_1496234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496247 : List Nat := [1, 1, 3, 1, 4, 1, 2, 1, 2, 7]
def baseStart_1496247 : Nat := 118140960795 + 1496247 * 2 ^ 59
def prefixEnd_1496247 : Nat := 4983230072969 + 3 ^ 40 * 1496247 * 2
def baseEnd_1496247 : Nat := 256097962949304220143797

theorem tailTrace_1496247 : CollatzResearch.WordTrace tailWord_1496247 prefixEnd_1496247 256097962949304220143797 := by
  unfold tailWord_1496247
  simp only [CollatzResearch.WordTrace]
  refine ⟨54572611410360132488238995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36381740940240088325492663 54572611410360132488238995)
  ·
    refine ⟨81858917115540198732358493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54572611410360132488238995 81858917115540198732358493)
    ·
      refine ⟨30697093918327574524634435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81858917115540198732358493 30697093918327574524634435)
      ·
        refine ⟨46045640877491361786951653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30697093918327574524634435 46045640877491361786951653)
        ·
          refine ⟨8633557664529630335053435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46045640877491361786951653 8633557664529630335053435)
          ·
            refine ⟨12950336496794445502580153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8633557664529630335053435 12950336496794445502580153)
            ·
              refine ⟨9712752372595834126935115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12950336496794445502580153 9712752372595834126935115)
              ·
                refine ⟨14569128558893751190402673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9712752372595834126935115 14569128558893751190402673)
                ·
                  refine ⟨10926846419170313392802005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14569128558893751190402673 10926846419170313392802005)
                  ·
                    refine ⟨256097962949304220143797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10926846419170313392802005 256097962949304220143797)
                    ·
                      rfl

theorem cell23_1496247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 7].length) (baseStart_1496247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1496247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1496247 prefixEnd_1496247 := by exact prefixLift 1496247
  have htrace : WordTrace (prefixWord ++ tailWord_1496247) baseStart_1496247 baseEnd_1496247 := by
    simpa [prefixWord, tailWord_1496247, baseEnd_1496247] using wordTrace_append hprefix tailTrace_1496247
  have hstable : (prefixWord ++ tailWord_1496247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496247).length < 2 ^ (prefixWord ++ tailWord_1496247).sum := by decide
  have hdescent : baseEnd_1496247 < baseStart_1496247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496267 : List Nat := [1, 1, 1, 1, 3, 2, 2, 1, 4, 3, 4]
def baseStart_1496267 : Nat := 118140960795 + 1496267 * 2 ^ 59
def prefixEnd_1496267 : Nat := 4983230072969 + 3 ^ 40 * 1496267 * 2
def baseEnd_1496267 : Nat := 768304158461002582181299

theorem tailTrace_1496267 : CollatzResearch.WordTrace tailWord_1496267 prefixEnd_1496267 768304158461002582181299 := by
  unfold tailWord_1496267
  simp only [CollatzResearch.WordTrace]
  refine ⟨54573340870287675903967055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36382227246858450602644703 54573340870287675903967055)
  ·
    refine ⟨81860011305431513855950583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54573340870287675903967055 81860011305431513855950583)
    ·
      refine ⟨122790016958147270783925875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81860011305431513855950583 122790016958147270783925875)
      ·
        refine ⟨184185025437220906175888813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122790016958147270783925875 184185025437220906175888813)
        ·
          refine ⟨69069384538957839815958305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184185025437220906175888813 69069384538957839815958305)
          ·
            refine ⟨51802038404218379861968729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69069384538957839815958305 51802038404218379861968729)
            ·
              refine ⟨38851528803163784896476547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51802038404218379861968729 38851528803163784896476547)
              ·
                refine ⟨58277293204745677344714821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38851528803163784896476547 58277293204745677344714821)
                ·
                  refine ⟨10926992475889814502134029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58277293204745677344714821 10926992475889814502134029)
                  ·
                    refine ⟨4097622178458680438300261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10926992475889814502134029 4097622178458680438300261)
                    ·
                      refine ⟨768304158461002582181299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4097622178458680438300261 768304158461002582181299)
                      ·
                        rfl

theorem cell23_1496267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 3, 4].length) (baseStart_1496267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1496267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1496267 prefixEnd_1496267 := by exact prefixLift 1496267
  have htrace : WordTrace (prefixWord ++ tailWord_1496267) baseStart_1496267 baseEnd_1496267 := by
    simpa [prefixWord, tailWord_1496267, baseEnd_1496267] using wordTrace_append hprefix tailTrace_1496267
  have hstable : (prefixWord ++ tailWord_1496267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496267).length < 2 ^ (prefixWord ++ tailWord_1496267).sum := by decide
  have hdescent : baseEnd_1496267 < baseStart_1496267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496271 : List Nat := [1, 1, 2, 1, 1, 3, 2, 6, 1, 3, 2]
def baseStart_1496271 : Nat := 118140960795 + 1496271 * 2 ^ 59
def prefixEnd_1496271 : Nat := 4983230072969 + 3 ^ 40 * 1496271 * 2
def baseEnd_1496271 : Nat := 768306212383620566531281

theorem tailTrace_1496271 : CollatzResearch.WordTrace tailWord_1496271 prefixEnd_1496271 768306212383620566531281 := by
  unfold tailWord_1496271
  simp only [CollatzResearch.WordTrace]
  refine ⟨54573486762273184587112667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36382324508182123058075111 54573486762273184587112667)
  ·
    refine ⟨81860230143409776880669001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54573486762273184587112667 81860230143409776880669001)
    ·
      refine ⟨61395172607557332660501751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81860230143409776880669001 61395172607557332660501751)
      ·
        refine ⟨92092758911335998990752627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61395172607557332660501751 92092758911335998990752627)
        ·
          refine ⟨138139138367003998486128941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92092758911335998990752627 138139138367003998486128941)
          ·
            refine ⟨51802176887626499432298353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138139138367003998486128941 51802176887626499432298353)
            ·
              refine ⟨38851632665719874574223765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51802176887626499432298353 38851632665719874574223765)
              ·
                refine ⟨1821170281205619120666739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 38851632665719874574223765 1821170281205619120666739)
                ·
                  refine ⟨2731755421808428681000109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1821170281205619120666739 2731755421808428681000109)
                  ·
                    refine ⟨1024408283178160755375041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2731755421808428681000109 1024408283178160755375041)
                    ·
                      refine ⟨768306212383620566531281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1024408283178160755375041 768306212383620566531281)
                      ·
                        rfl

theorem cell23_1496271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 6, 1, 3, 2].length) (baseStart_1496271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1496271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1496271 prefixEnd_1496271 := by exact prefixLift 1496271
  have htrace : WordTrace (prefixWord ++ tailWord_1496271) baseStart_1496271 baseEnd_1496271 := by
    simpa [prefixWord, tailWord_1496271, baseEnd_1496271] using wordTrace_append hprefix tailTrace_1496271
  have hstable : (prefixWord ++ tailWord_1496271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496271).length < 2 ^ (prefixWord ++ tailWord_1496271).sum := by decide
  have hdescent : baseEnd_1496271 < baseStart_1496271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496295 : List Nat := [1, 1, 5, 3, 2, 1, 2, 2, 2, 1, 3]
def baseStart_1496295 : Nat := 118140960795 + 1496295 * 2 ^ 59
def prefixEnd_1496295 : Nat := 4983230072969 + 3 ^ 40 * 1496295 * 2
def baseEnd_1496295 : Nat := 768318535919328472631171

theorem tailTrace_1496295 : CollatzResearch.WordTrace tailWord_1496295 prefixEnd_1496295 768318535919328472631171 := by
  unfold tailWord_1496295
  simp only [CollatzResearch.WordTrace]
  refine ⟨54574362114186236685986339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36382908076124157790657559 54574362114186236685986339)
  ·
    refine ⟨81861543171279355028979509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54574362114186236685986339 81861543171279355028979509)
    ·
      refine ⟨7674519672307439533966829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81861543171279355028979509 7674519672307439533966829)
      ·
        refine ⟨2877944877115289825237561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7674519672307439533966829 2877944877115289825237561)
        ·
          refine ⟨2158458657836467368928171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2877944877115289825237561 2158458657836467368928171)
          ·
            refine ⟨3237687986754701053392257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2158458657836467368928171 3237687986754701053392257)
            ·
              refine ⟨2428265990066025790044193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3237687986754701053392257 2428265990066025790044193)
              ·
                refine ⟨1821199492549519342533145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2428265990066025790044193 1821199492549519342533145)
                ·
                  refine ⟨1365899619412139506899859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1821199492549519342533145 1365899619412139506899859)
                  ·
                    refine ⟨2048849429118209260349789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1365899619412139506899859 2048849429118209260349789)
                    ·
                      refine ⟨768318535919328472631171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2048849429118209260349789 768318535919328472631171)
                      ·
                        rfl

theorem cell23_1496295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_1496295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1496295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1496295 prefixEnd_1496295 := by exact prefixLift 1496295
  have htrace : WordTrace (prefixWord ++ tailWord_1496295) baseStart_1496295 baseEnd_1496295 := by
    simpa [prefixWord, tailWord_1496295, baseEnd_1496295] using wordTrace_append hprefix tailTrace_1496295
  have hstable : (prefixWord ++ tailWord_1496295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496295).length < 2 ^ (prefixWord ++ tailWord_1496295).sum := by decide
  have hdescent : baseEnd_1496295 < baseStart_1496295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496314 : List Nat := [3, 1, 1, 1, 1, 4, 3, 1, 2, 2, 4]
def baseStart_1496314 : Nat := 118140960795 + 1496314 * 2 ^ 59
def prefixEnd_1496314 : Nat := 4983230072969 + 3 ^ 40 * 1496314 * 2
def baseEnd_1496314 : Nat := 768328292051763898293583

theorem tailTrace_1496314 : CollatzResearch.WordTrace tailWord_1496314 prefixEnd_1496314 768328292051763898293583 := by
  unfold tailWord_1496314
  simp only [CollatzResearch.WordTrace]
  refine ⟨13643763775279350732731999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36383370067411601953951997 13643763775279350732731999)
  ·
    refine ⟨20465645662919026099097999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13643763775279350732731999 20465645662919026099097999)
    ·
      refine ⟨30698468494378539148646999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20465645662919026099097999 30698468494378539148646999)
      ·
        refine ⟨46047702741567808722970499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30698468494378539148646999 46047702741567808722970499)
        ·
          refine ⟨69071554112351713084455749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46047702741567808722970499 69071554112351713084455749)
          ·
            refine ⟨12950916396065946203335453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69071554112351713084455749 12950916396065946203335453)
            ·
              refine ⟨4856593648524729826250795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12950916396065946203335453 4856593648524729826250795)
              ·
                refine ⟨7284890472787094739376193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4856593648524729826250795 7284890472787094739376193)
                ·
                  refine ⟨5463667854590321054532145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7284890472787094739376193 5463667854590321054532145)
                  ·
                    refine ⟨4097750890942740790899109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5463667854590321054532145 4097750890942740790899109)
                    ·
                      refine ⟨768328292051763898293583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4097750890942740790899109 768328292051763898293583)
                      ·
                        rfl

theorem cell23_1496314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 2, 2, 4].length) (baseStart_1496314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1496314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1496314 prefixEnd_1496314 := by exact prefixLift 1496314
  have htrace : WordTrace (prefixWord ++ tailWord_1496314) baseStart_1496314 baseEnd_1496314 := by
    simpa [prefixWord, tailWord_1496314, baseEnd_1496314] using wordTrace_append hprefix tailTrace_1496314
  have hstable : (prefixWord ++ tailWord_1496314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496314).length < 2 ^ (prefixWord ++ tailWord_1496314).sum := by decide
  have hdescent : baseEnd_1496314 < baseStart_1496314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496318 : List Nat := [4, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2]
def baseStart_1496318 : Nat := 118140960795 + 1496318 * 2 ^ 59
def prefixEnd_1496318 : Nat := 4983230072969 + 3 ^ 40 * 1496318 * 2
def baseEnd_1496318 : Nat := 768330345974381882643565

theorem tailTrace_1496318 : CollatzResearch.WordTrace tailWord_1496318 prefixEnd_1496318 768330345974381882643565 := by
  unfold tailWord_1496318
  simp only [CollatzResearch.WordTrace]
  refine ⟨6821900124137863951759201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36383467328735274409382405 6821900124137863951759201)
  ·
    refine ⟨5116425093103397963819401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6821900124137863951759201 5116425093103397963819401)
    ·
      refine ⟨3837318819827548472864551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5116425093103397963819401 3837318819827548472864551)
      ·
        refine ⟨5755978229741322709296827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3837318819827548472864551 5755978229741322709296827)
        ·
          refine ⟨8633967344611984063945241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5755978229741322709296827 8633967344611984063945241)
          ·
            refine ⟨6475475508458988047958931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8633967344611984063945241 6475475508458988047958931)
            ·
              refine ⟨9713213262688482071938397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6475475508458988047958931 9713213262688482071938397)
              ·
                refine ⟨3642454973508180776976899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9713213262688482071938397 3642454973508180776976899)
                ·
                  refine ⟨5463682460262271165465349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3642454973508180776976899 5463682460262271165465349)
                  ·
                    refine ⟨1024440461299175843524753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5463682460262271165465349 1024440461299175843524753)
                    ·
                      refine ⟨768330345974381882643565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1024440461299175843524753 768330345974381882643565)
                      ·
                        rfl

theorem cell23_1496318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2].length) (baseStart_1496318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1496318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1496318 prefixEnd_1496318 := by exact prefixLift 1496318
  have htrace : WordTrace (prefixWord ++ tailWord_1496318) baseStart_1496318 baseEnd_1496318 := by
    simpa [prefixWord, tailWord_1496318, baseEnd_1496318] using wordTrace_append hprefix tailTrace_1496318
  have hstable : (prefixWord ++ tailWord_1496318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496318).length < 2 ^ (prefixWord ++ tailWord_1496318).sum := by decide
  have hdescent : baseEnd_1496318 < baseStart_1496318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496324 : List Nat := [2, 3, 2, 2, 2, 1, 1, 1, 9]
def baseStart_1496324 : Nat := 118140960795 + 1496324 * 2 ^ 59
def prefixEnd_1496324 : Nat := 4983230072969 + 3 ^ 40 * 1496324 * 2
def baseEnd_1496324 : Nat := 85370380762034317685393

theorem tailTrace_1496324 : CollatzResearch.WordTrace tailWord_1496324 prefixEnd_1496324 85370380762034317685393 := by
  unfold tailWord_1496324
  simp only [CollatzResearch.WordTrace]
  refine ⟨27287709915540587319396013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36383613220720783092528017 27287709915540587319396013)
  ·
    refine ⟨10232891218327720244773505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27287709915540587319396013 10232891218327720244773505)
    ·
      refine ⟨7674668413745790183580129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10232891218327720244773505 7674668413745790183580129)
      ·
        refine ⟨5756001310309342637685097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7674668413745790183580129 5756001310309342637685097)
        ·
          refine ⟨4317000982732006978263823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5756001310309342637685097 4317000982732006978263823)
          ·
            refine ⟨6475501474098010467395735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4317000982732006978263823 6475501474098010467395735)
            ·
              refine ⟨9713252211147015701093603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6475501474098010467395735 9713252211147015701093603)
              ·
                refine ⟨14569878316720523551640405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9713252211147015701093603 14569878316720523551640405)
                ·
                  refine ⟨85370380762034317685393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 14569878316720523551640405 85370380762034317685393)
                  ·
                    rfl

theorem cell23_1496324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 9].length) (baseStart_1496324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1496324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1496324 prefixEnd_1496324 := by exact prefixLift 1496324
  have htrace : WordTrace (prefixWord ++ tailWord_1496324) baseStart_1496324 baseEnd_1496324 := by
    simpa [prefixWord, tailWord_1496324, baseEnd_1496324] using wordTrace_append hprefix tailTrace_1496324
  have hstable : (prefixWord ++ tailWord_1496324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496324).length < 2 ^ (prefixWord ++ tailWord_1496324).sum := by decide
  have hdescent : baseEnd_1496324 < baseStart_1496324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496352 : List Nat := [2, 1, 1, 5, 3, 2, 1, 2, 2, 2, 2]
def baseStart_1496352 : Nat := 118140960795 + 1496352 * 2 ^ 59
def prefixEnd_1496352 : Nat := 4983230072969 + 3 ^ 40 * 1496352 * 2
def baseEnd_1496352 : Nat := 768347804316634749618409

theorem tailTrace_1496352 : CollatzResearch.WordTrace tailWord_1496352 prefixEnd_1496352 768347804316634749618409 := by
  unfold tailWord_1496352
  simp only [CollatzResearch.WordTrace]
  refine ⟨27288220537489867710405655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36384294049986490280540873 27288220537489867710405655)
  ·
    refine ⟨40932330806234801565608483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27288220537489867710405655 40932330806234801565608483)
    ·
      refine ⟨61398496209352202348412725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40932330806234801565608483 61398496209352202348412725)
      ·
        refine ⟨5756109019626768970163693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61398496209352202348412725 5756109019626768970163693)
        ·
          refine ⟨2158540882360038363811385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5756109019626768970163693 2158540882360038363811385)
          ·
            refine ⟨1618905661770028772858539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2158540882360038363811385 1618905661770028772858539)
            ·
              refine ⟨2428358492655043159287809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1618905661770028772858539 2428358492655043159287809)
              ·
                refine ⟨1821268869491282369465857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2428358492655043159287809 1821268869491282369465857)
                ·
                  refine ⟨1365951652118461777099393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1821268869491282369465857 1365951652118461777099393)
                  ·
                    refine ⟨1024463739088846332824545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1365951652118461777099393 1024463739088846332824545)
                    ·
                      refine ⟨768347804316634749618409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1024463739088846332824545 768347804316634749618409)
                      ·
                        rfl

theorem cell23_1496352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 2, 2, 2, 2].length) (baseStart_1496352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1496352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1496352 prefixEnd_1496352 := by exact prefixLift 1496352
  have htrace : WordTrace (prefixWord ++ tailWord_1496352) baseStart_1496352 baseEnd_1496352 := by
    simpa [prefixWord, tailWord_1496352, baseEnd_1496352] using wordTrace_append hprefix tailTrace_1496352
  have hstable : (prefixWord ++ tailWord_1496352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496352).length < 2 ^ (prefixWord ++ tailWord_1496352).sum := by decide
  have hdescent : baseEnd_1496352 < baseStart_1496352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496504 : List Nat := [2, 1, 2, 1, 2, 2, 2, 11]
def baseStart_1496504 : Nat := 118140960795 + 1496504 * 2 ^ 59
def prefixEnd_1496504 : Nat := 4983230072969 + 3 ^ 40 * 1496504 * 2
def baseEnd_1496504 : Nat := 28460216791708079811767

theorem tailTrace_1496504 : CollatzResearch.WordTrace tailWord_1496504 prefixEnd_1496504 28460216791708079811767 := by
  unfold tailWord_1496504
  simp only [CollatzResearch.WordTrace]
  refine ⟨27290992485214532690172283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36387989980286043586896377 27290992485214532690172283)
  ·
    refine ⟨40936488727821799035258425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27290992485214532690172283 40936488727821799035258425)
    ·
      refine ⟨30702366545866349276443819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40936488727821799035258425 30702366545866349276443819)
      ·
        refine ⟨46053549818799523914665729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30702366545866349276443819 46053549818799523914665729)
        ·
          refine ⟨34540162364099642935999297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46053549818799523914665729 34540162364099642935999297)
          ·
            refine ⟨25905121773074732201999473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34540162364099642935999297 25905121773074732201999473)
            ·
              refine ⟨19428841329806049151499605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25905121773074732201999473 19428841329806049151499605)
              ·
                refine ⟨28460216791708079811767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 19428841329806049151499605 28460216791708079811767)
                ·
                  rfl

theorem cell23_1496504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 11].length) (baseStart_1496504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1496504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1496504 prefixEnd_1496504 := by exact prefixLift 1496504
  have htrace : WordTrace (prefixWord ++ tailWord_1496504) baseStart_1496504 baseEnd_1496504 := by
    simpa [prefixWord, tailWord_1496504, baseEnd_1496504] using wordTrace_append hprefix tailTrace_1496504
  have hstable : (prefixWord ++ tailWord_1496504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496504).length < 2 ^ (prefixWord ++ tailWord_1496504).sum := by decide
  have hdescent : baseEnd_1496504 < baseStart_1496504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496561 : List Nat := [1, 2, 2, 2, 3, 2, 1, 1, 2, 2, 5]
def baseStart_1496561 : Nat := 118140960795 + 1496561 * 2 ^ 59
def prefixEnd_1496561 : Nat := 4983230072969 + 3 ^ 40 * 1496561 * 2
def baseEnd_1496561 : Nat := 768455121773424431904947

theorem tailTrace_1496561 : CollatzResearch.WordTrace tailWord_1496561 prefixEnd_1496561 768455121773424431904947 := by
  unfold tailWord_1496561
  simp only [CollatzResearch.WordTrace]
  refine ⟨54584063931222564115169537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36389375954148376076779691 54584063931222564115169537)
  ·
    refine ⟨40938047948416923086377153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54584063931222564115169537 40938047948416923086377153)
    ·
      refine ⟨30703535961312692314782865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40938047948416923086377153 30703535961312692314782865)
      ·
        refine ⟨23027651970984519236087149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30703535961312692314782865 23027651970984519236087149)
        ·
          refine ⟨8635369489119194713532681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23027651970984519236087149 8635369489119194713532681)
          ·
            refine ⟨6476527116839396035149511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8635369489119194713532681 6476527116839396035149511)
            ·
              refine ⟨9714790675259094052724267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6476527116839396035149511 9714790675259094052724267)
              ·
                refine ⟨14572186012888641079086401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9714790675259094052724267 14572186012888641079086401)
                ·
                  refine ⟨10929139509666480809314801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14572186012888641079086401 10929139509666480809314801)
                  ·
                    refine ⟨8196854632249860606986101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10929139509666480809314801 8196854632249860606986101)
                    ·
                      refine ⟨768455121773424431904947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8196854632249860606986101 768455121773424431904947)
                      ·
                        rfl

theorem cell23_1496561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 2, 5].length) (baseStart_1496561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1496561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1496561 prefixEnd_1496561 := by exact prefixLift 1496561
  have htrace : WordTrace (prefixWord ++ tailWord_1496561) baseStart_1496561 baseEnd_1496561 := by
    simpa [prefixWord, tailWord_1496561, baseEnd_1496561] using wordTrace_append hprefix tailTrace_1496561
  have hstable : (prefixWord ++ tailWord_1496561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496561).length < 2 ^ (prefixWord ++ tailWord_1496561).sum := by decide
  have hdescent : baseEnd_1496561 < baseStart_1496561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496566 : List Nat := [5, 1, 1, 1, 2, 4, 1, 3, 1, 2, 2]
def baseStart_1496566 : Nat := 118140960795 + 1496566 * 2 ^ 59
def prefixEnd_1496566 : Nat := 4983230072969 + 3 ^ 40 * 1496566 * 2
def baseEnd_1496566 : Nat := 768457689176696912342425

theorem tailTrace_1496566 : CollatzResearch.WordTrace tailWord_1496566 prefixEnd_1496566 768457689176696912342425 := by
  unfold tailWord_1496566
  simp only [CollatzResearch.WordTrace]
  refine ⟨3411515393512778123068847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36389497530802966646067701 3411515393512778123068847)
  ·
    refine ⟨5117273090269167184603271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3411515393512778123068847 5117273090269167184603271)
    ·
      refine ⟨7675909635403750776904907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5117273090269167184603271 7675909635403750776904907)
      ·
        refine ⟨11513864453105626165357361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7675909635403750776904907 11513864453105626165357361)
        ·
          refine ⟨8635398339829219624018021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11513864453105626165357361 8635398339829219624018021)
          ·
            refine ⟨1619137188717978679503379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8635398339829219624018021 1619137188717978679503379)
            ·
              refine ⟨2428705783076968019255069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1619137188717978679503379 2428705783076968019255069)
              ·
                refine ⟨910764668653863007220651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2428705783076968019255069 910764668653863007220651)
                ·
                  refine ⟨1366147002980794510830977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 910764668653863007220651 1366147002980794510830977)
                  ·
                    refine ⟨1024610252235595883123233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1366147002980794510830977 1024610252235595883123233)
                    ·
                      refine ⟨768457689176696912342425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1024610252235595883123233 768457689176696912342425)
                      ·
                        rfl

theorem cell23_1496566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 3, 1, 2, 2].length) (baseStart_1496566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1496566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1496566 prefixEnd_1496566 := by exact prefixLift 1496566
  have htrace : WordTrace (prefixWord ++ tailWord_1496566) baseStart_1496566 baseEnd_1496566 := by
    simpa [prefixWord, tailWord_1496566, baseEnd_1496566] using wordTrace_append hprefix tailTrace_1496566
  have hstable : (prefixWord ++ tailWord_1496566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496566).length < 2 ^ (prefixWord ++ tailWord_1496566).sum := by decide
  have hdescent : baseEnd_1496566 < baseStart_1496566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496605 : List Nat := [1, 4, 2, 2, 1, 1, 2, 3, 1, 4, 2]
def baseStart_1496605 : Nat := 118140960795 + 1496605 * 2 ^ 59
def prefixEnd_1496605 : Nat := 4983230072969 + 3 ^ 40 * 1496605 * 2
def baseEnd_1496605 : Nat := 768477714922222259754745

theorem tailTrace_1496605 : CollatzResearch.WordTrace tailWord_1496605 prefixEnd_1496605 768477714922222259754745 := by
  unfold tailWord_1496605
  simp only [CollatzResearch.WordTrace]
  refine ⟨54585668743063159629771269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36390445828708773086514179 54585668743063159629771269)
  ·
    refine ⟨10234812889324342430582113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54585668743063159629771269 10234812889324342430582113)
    ·
      refine ⟨7676109666993256822936585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10234812889324342430582113 7676109666993256822936585)
      ·
        refine ⟨5757082250244942617202439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7676109666993256822936585 5757082250244942617202439)
        ·
          refine ⟨8635623375367413925803659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5757082250244942617202439 8635623375367413925803659)
          ·
            refine ⟨12953435063051120888705489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8635623375367413925803659 12953435063051120888705489)
            ·
              refine ⟨9715076297288340666529117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12953435063051120888705489 9715076297288340666529117)
              ·
                refine ⟨3643153611483127749948419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9715076297288340666529117 3643153611483127749948419)
                ·
                  refine ⟨5464730417224691624922629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3643153611483127749948419 5464730417224691624922629)
                  ·
                    refine ⟨1024636953229629679672993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5464730417224691624922629 1024636953229629679672993)
                    ·
                      refine ⟨768477714922222259754745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1024636953229629679672993 768477714922222259754745)
                      ·
                        rfl

theorem cell23_1496605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 3, 1, 4, 2].length) (baseStart_1496605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1496605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1496605 prefixEnd_1496605 := by exact prefixLift 1496605
  have htrace : WordTrace (prefixWord ++ tailWord_1496605) baseStart_1496605 baseEnd_1496605 := by
    simpa [prefixWord, tailWord_1496605, baseEnd_1496605] using wordTrace_append hprefix tailTrace_1496605
  have hstable : (prefixWord ++ tailWord_1496605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496605).length < 2 ^ (prefixWord ++ tailWord_1496605).sum := by decide
  have hdescent : baseEnd_1496605 < baseStart_1496605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496608 : List Nat := [2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 5]
def baseStart_1496608 : Nat := 118140960795 + 1496608 * 2 ^ 59
def prefixEnd_1496608 : Nat := 4983230072969 + 3 ^ 40 * 1496608 * 2
def baseEnd_1496608 : Nat := 768479255364185748017231

theorem tailTrace_1496608 : CollatzResearch.WordTrace tailWord_1496608 prefixEnd_1496608 768479255364185748017231 := by
  unfold tailWord_1496608
  simp only [CollatzResearch.WordTrace]
  refine ⟨27292889081026145571065239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36390518774701527428086985 27292889081026145571065239)
  ·
    refine ⟨40939333621539218356597859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27292889081026145571065239 40939333621539218356597859)
    ·
      refine ⟨61409000432308827534896789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40939333621539218356597859 61409000432308827534896789)
      ·
        refine ⟨2878546895264476290698287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 61409000432308827534896789 2878546895264476290698287)
        ·
          refine ⟨4317820342896714436047431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2878546895264476290698287 4317820342896714436047431)
          ·
            refine ⟨6476730514345071654071147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4317820342896714436047431 6476730514345071654071147)
            ·
              refine ⟨9715095771517607481106721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6476730514345071654071147 9715095771517607481106721)
              ·
                refine ⟨7286321828638205610830041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9715095771517607481106721 7286321828638205610830041)
                ·
                  refine ⟨5464741371478654208122531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7286321828638205610830041 5464741371478654208122531)
                  ·
                    refine ⟨8197112057217981312183797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5464741371478654208122531 8197112057217981312183797)
                    ·
                      refine ⟨768479255364185748017231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8197112057217981312183797 768479255364185748017231)
                      ·
                        rfl

theorem cell23_1496608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_1496608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1496608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1496608 prefixEnd_1496608 := by exact prefixLift 1496608
  have htrace : WordTrace (prefixWord ++ tailWord_1496608) baseStart_1496608 baseEnd_1496608 := by
    simpa [prefixWord, tailWord_1496608, baseEnd_1496608] using wordTrace_append hprefix tailTrace_1496608
  have hstable : (prefixWord ++ tailWord_1496608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496608).length < 2 ^ (prefixWord ++ tailWord_1496608).sum := by decide
  have hdescent : baseEnd_1496608 < baseStart_1496608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496622 : List Nat := [4, 1, 3, 1, 2, 2, 1, 2, 1, 4, 2]
def baseStart_1496622 : Nat := 118140960795 + 1496622 * 2 ^ 59
def prefixEnd_1496622 : Nat := 4983230072969 + 3 ^ 40 * 1496622 * 2
def baseEnd_1496622 : Nat := 768486444093348693242167

theorem tailTrace_1496622 : CollatzResearch.WordTrace tailWord_1496622 prefixEnd_1496622 768486444093348693242167 := by
  unfold tailWord_1496622
  simp only [CollatzResearch.WordTrace]
  refine ⟨6823286098000196441642515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36390859189334381022093413 6823286098000196441642515)
  ·
    refine ⟨10234929147000294662463773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6823286098000196441642515 10234929147000294662463773)
    ·
      refine ⟨3838098430125110498423915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10234929147000294662463773 3838098430125110498423915)
      ·
        refine ⟨5757147645187665747635873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3838098430125110498423915 5757147645187665747635873)
        ·
          refine ⟨4317860733890749310726905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5757147645187665747635873 4317860733890749310726905)
          ·
            refine ⟨3238395550418061983045179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4317860733890749310726905 3238395550418061983045179)
            ·
              refine ⟨4857593325627092974567769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3238395550418061983045179 4857593325627092974567769)
              ·
                refine ⟨3643194994220319730925827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4857593325627092974567769 3643194994220319730925827)
                ·
                  refine ⟨5464792491330479596388741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3643194994220319730925827 5464792491330479596388741)
                  ·
                    refine ⟨1024648592124464924322889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5464792491330479596388741 1024648592124464924322889)
                    ·
                      refine ⟨768486444093348693242167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1024648592124464924322889 768486444093348693242167)
                      ·
                        rfl

theorem cell23_1496622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 2, 1, 4, 2].length) (baseStart_1496622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1496622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1496622 prefixEnd_1496622 := by exact prefixLift 1496622
  have htrace : WordTrace (prefixWord ++ tailWord_1496622) baseStart_1496622 baseEnd_1496622 := by
    simpa [prefixWord, tailWord_1496622, baseEnd_1496622] using wordTrace_append hprefix tailTrace_1496622
  have hstable : (prefixWord ++ tailWord_1496622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496622).length < 2 ^ (prefixWord ++ tailWord_1496622).sum := by decide
  have hdescent : baseEnd_1496622 < baseStart_1496622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496675 : List Nat := [1, 1, 1, 5, 1, 5, 1, 1, 2, 5]
def baseStart_1496675 : Nat := 118140960795 + 1496675 * 2 ^ 59
def prefixEnd_1496675 : Nat := 4983230072969 + 3 ^ 40 * 1496675 * 2
def baseEnd_1496675 : Nat := 256171219522678995293141

theorem tailTrace_1496675 : CollatzResearch.WordTrace tailWord_1496675 prefixEnd_1496675 256171219522678995293141 := by
  unfold tailWord_1496675
  simp only [CollatzResearch.WordTrace]
  refine ⟨54588221852809561584819479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36392147901873041056546319 54588221852809561584819479)
  ·
    refine ⟨81882332779214342377229219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54588221852809561584819479 81882332779214342377229219)
    ·
      refine ⟨122823499168821513565843829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81882332779214342377229219 122823499168821513565843829)
      ·
        refine ⟨11514703047077016896797859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 122823499168821513565843829 11514703047077016896797859)
        ·
          refine ⟨17272054570615525345196789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11514703047077016896797859 17272054570615525345196789)
          ·
            refine ⟨1619255115995205501112199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17272054570615525345196789 1619255115995205501112199)
            ·
              refine ⟨2428882673992808251668299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1619255115995205501112199 2428882673992808251668299)
              ·
                refine ⟨3643324010989212377502449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2428882673992808251668299 3643324010989212377502449)
                ·
                  refine ⟨2732493008241909283126837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3643324010989212377502449 2732493008241909283126837)
                  ·
                    refine ⟨256171219522678995293141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2732493008241909283126837 256171219522678995293141)
                    ·
                      rfl

theorem cell23_1496675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 1, 2, 5].length) (baseStart_1496675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1496675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1496675 prefixEnd_1496675 := by exact prefixLift 1496675
  have htrace : WordTrace (prefixWord ++ tailWord_1496675) baseStart_1496675 baseEnd_1496675 := by
    simpa [prefixWord, tailWord_1496675, baseEnd_1496675] using wordTrace_append hprefix tailTrace_1496675
  have hstable : (prefixWord ++ tailWord_1496675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496675).length < 2 ^ (prefixWord ++ tailWord_1496675).sum := by decide
  have hdescent : baseEnd_1496675 < baseStart_1496675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496705 : List Nat := [1, 2, 4, 2, 1, 2, 1, 3, 3, 4]
def baseStart_1496705 : Nat := 118140960795 + 1496705 * 2 ^ 59
def prefixEnd_1496705 : Nat := 4983230072969 + 3 ^ 40 * 1496705 * 2
def baseEnd_1496705 : Nat := 256176354329223956168095

theorem tailTrace_1496705 : CollatzResearch.WordTrace tailWord_1496705 prefixEnd_1496705 256176354329223956168095 := by
  unfold tailWord_1496705
  simp only [CollatzResearch.WordTrace]
  refine ⟨54589316042700876708411569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36392877361800584472274379 54589316042700876708411569)
  ·
    refine ⟨40941987032025657531308677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54589316042700876708411569 40941987032025657531308677)
    ·
      refine ⟨7676622568504810787120377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40941987032025657531308677 7676622568504810787120377)
      ·
        refine ⟨5757466926378608090340283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7676622568504810787120377 5757466926378608090340283)
        ·
          refine ⟨8636200389567912135510425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5757466926378608090340283 8636200389567912135510425)
          ·
            refine ⟨6477150292175934101632819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8636200389567912135510425 6477150292175934101632819)
            ·
              refine ⟨9715725438263901152449229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6477150292175934101632819 9715725438263901152449229)
              ·
                refine ⟨3643397039348962932168461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9715725438263901152449229 3643397039348962932168461)
                ·
                  refine ⟨1366273889755861099563173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3643397039348962932168461 1366273889755861099563173)
                  ·
                    refine ⟨256176354329223956168095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1366273889755861099563173 256176354329223956168095)
                    ·
                      rfl

theorem cell23_1496705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 3, 3, 4].length) (baseStart_1496705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1496705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1496705 prefixEnd_1496705 := by exact prefixLift 1496705
  have htrace : WordTrace (prefixWord ++ tailWord_1496705) baseStart_1496705 baseEnd_1496705 := by
    simpa [prefixWord, tailWord_1496705, baseEnd_1496705] using wordTrace_append hprefix tailTrace_1496705
  have hstable : (prefixWord ++ tailWord_1496705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496705).length < 2 ^ (prefixWord ++ tailWord_1496705).sum := by decide
  have hdescent : baseEnd_1496705 < baseStart_1496705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496762 : List Nat := [3, 1, 1, 1, 2, 4, 3, 1, 3, 1, 3]
def baseStart_1496762 : Nat := 118140960795 + 1496762 * 2 ^ 59
def prefixEnd_1496762 : Nat := 4983230072969 + 3 ^ 40 * 1496762 * 2
def baseEnd_1496762 : Nat := 768558331384978145491523

theorem tailTrace_1496762 : CollatzResearch.WordTrace tailWord_1496762 prefixEnd_1496762 768558331384978145491523 := by
  unfold tailWord_1496762
  simp only [CollatzResearch.WordTrace]
  refine ⟨13647848750873593860809135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36394263335662916962157693 13647848750873593860809135)
  ·
    refine ⟨20471773126310390791213703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13647848750873593860809135 20471773126310390791213703)
    ·
      refine ⟨30707659689465586186820555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20471773126310390791213703 30707659689465586186820555)
      ·
        refine ⟨46061489534198379280230833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30707659689465586186820555 46061489534198379280230833)
        ·
          refine ⟨34546117150648784460173125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46061489534198379280230833 34546117150648784460173125)
          ·
            refine ⟨6477396965746647086282461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34546117150648784460173125 6477396965746647086282461)
            ·
              refine ⟨2429023862154992657355923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6477396965746647086282461 2429023862154992657355923)
              ·
                refine ⟨3643535793232488986033885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2429023862154992657355923 3643535793232488986033885)
                ·
                  refine ⟨1366325922462183369762707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3643535793232488986033885 1366325922462183369762707)
                  ·
                    refine ⟨2049488883693275054644061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1366325922462183369762707 2049488883693275054644061)
                    ·
                      refine ⟨768558331384978145491523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2049488883693275054644061 768558331384978145491523)
                      ·
                        rfl

theorem cell23_1496762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 1, 3, 1, 3].length) (baseStart_1496762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1496762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1496762 prefixEnd_1496762 := by exact prefixLift 1496762
  have htrace : WordTrace (prefixWord ++ tailWord_1496762) baseStart_1496762 baseEnd_1496762 := by
    simpa [prefixWord, tailWord_1496762, baseEnd_1496762] using wordTrace_append hprefix tailTrace_1496762
  have hstable : (prefixWord ++ tailWord_1496762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496762).length < 2 ^ (prefixWord ++ tailWord_1496762).sum := by decide
  have hdescent : baseEnd_1496762 < baseStart_1496762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496772 : List Nat := [2, 3, 3, 1, 1, 1, 1, 2, 4, 3, 2]
def baseStart_1496772 : Nat := 118140960795 + 1496772 * 2 ^ 59
def prefixEnd_1496772 : Nat := 4983230072969 + 3 ^ 40 * 1496772 * 2
def baseEnd_1496772 : Nat := 768563466191523106366477

theorem tailTrace_1496772 : CollatzResearch.WordTrace tailWord_1496772 prefixEnd_1496772 768563466191523106366477 := by
  unfold tailWord_1496772
  simp only [CollatzResearch.WordTrace]
  refine ⟨27295879866729073575550285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36394506488972098100733713 27295879866729073575550285)
  ·
    refine ⟨10235954950023402590831357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27295879866729073575550285 10235954950023402590831357)
    ·
      refine ⟨3838483106258775971561759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10235954950023402590831357 3838483106258775971561759)
      ·
        refine ⟨5757724659388163957342639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3838483106258775971561759 5757724659388163957342639)
        ·
          refine ⟨8636586989082245936013959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5757724659388163957342639 8636586989082245936013959)
          ·
            refine ⟨12954880483623368904020939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8636586989082245936013959 12954880483623368904020939)
            ·
              refine ⟨19432320725435053356031409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12954880483623368904020939 19432320725435053356031409)
              ·
                refine ⟨14574240544076290017023557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19432320725435053356031409 14574240544076290017023557)
                ·
                  refine ⟨2732670102014304378191917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14574240544076290017023557 2732670102014304378191917)
                  ·
                    refine ⟨1024751288255364141821969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2732670102014304378191917 1024751288255364141821969)
                    ·
                      refine ⟨768563466191523106366477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1024751288255364141821969 768563466191523106366477)
                      ·
                        rfl

theorem cell23_1496772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 4, 3, 2].length) (baseStart_1496772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1496772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1496772 prefixEnd_1496772 := by exact prefixLift 1496772
  have htrace : WordTrace (prefixWord ++ tailWord_1496772) baseStart_1496772 baseEnd_1496772 := by
    simpa [prefixWord, tailWord_1496772, baseEnd_1496772] using wordTrace_append hprefix tailTrace_1496772
  have hstable : (prefixWord ++ tailWord_1496772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496772).length < 2 ^ (prefixWord ++ tailWord_1496772).sum := by decide
  have hdescent : baseEnd_1496772 < baseStart_1496772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496785 : List Nat := [1, 2, 2, 1, 2, 5, 1, 1, 3, 1, 4]
def baseStart_1496785 : Nat := 118140960795 + 1496785 * 2 ^ 59
def prefixEnd_1496785 : Nat := 4983230072969 + 3 ^ 40 * 1496785 * 2
def baseEnd_1496785 : Nat := 768570141440031555503917

theorem tailTrace_1496785 : CollatzResearch.WordTrace tailWord_1496785 prefixEnd_1496785 768570141440031555503917 := by
  unfold tailWord_1496785
  simp only [CollatzResearch.WordTrace]
  refine ⟨54592233882411050371323809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36394822588274033580882539 54592233882411050371323809)
  ·
    refine ⟨40944175411808287778492857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54592233882411050371323809 40944175411808287778492857)
    ·
      refine ⟨30708131558856215833869643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40944175411808287778492857 30708131558856215833869643)
      ·
        refine ⟨46062197338284323750804465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30708131558856215833869643 46062197338284323750804465)
        ·
          refine ⟨34546648003713242813103349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46062197338284323750804465 34546648003713242813103349)
          ·
            refine ⟨3238748250348116513728439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34546648003713242813103349 3238748250348116513728439)
            ·
              refine ⟨4858122375522174770592659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3238748250348116513728439 4858122375522174770592659)
              ·
                refine ⟨7287183563283262155888989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4858122375522174770592659 7287183563283262155888989)
                ·
                  refine ⟨2732693836231223308458371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7287183563283262155888989 2732693836231223308458371)
                  ·
                    refine ⟨4099040754346834962687557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2732693836231223308458371 4099040754346834962687557)
                    ·
                      refine ⟨768570141440031555503917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4099040754346834962687557 768570141440031555503917)
                      ·
                        rfl

theorem cell23_1496785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 3, 1, 4].length) (baseStart_1496785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1496785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1496785 prefixEnd_1496785 := by exact prefixLift 1496785
  have htrace : WordTrace (prefixWord ++ tailWord_1496785) baseStart_1496785 baseEnd_1496785 := by
    simpa [prefixWord, tailWord_1496785, baseEnd_1496785] using wordTrace_append hprefix tailTrace_1496785
  have hstable : (prefixWord ++ tailWord_1496785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496785).length < 2 ^ (prefixWord ++ tailWord_1496785).sum := by decide
  have hdescent : baseEnd_1496785 < baseStart_1496785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1496808 : List Nat := [2, 1, 4, 1, 3, 12]
def baseStart_1496808 : Nat := 118140960795 + 1496808 * 2 ^ 59
def prefixEnd_1496808 : Nat := 4983230072969 + 3 ^ 40 * 1496808 * 2
def baseEnd_1496808 : Nat := 3162888689280185043277

theorem tailTrace_1496808 : CollatzResearch.WordTrace tailWord_1496808 prefixEnd_1496808 3162888689280185043277 := by
  unfold tailWord_1496808
  simp only [CollatzResearch.WordTrace]
  refine ⟨27296536380663862649705539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36395381840885150199607385 27296536380663862649705539)
  ·
    refine ⟨40944804570995793974558309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27296536380663862649705539 40944804570995793974558309)
    ·
      refine ⟨7677150857061711370229683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40944804570995793974558309 7677150857061711370229683)
      ·
        refine ⟨11515726285592567055344525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7677150857061711370229683 11515726285592567055344525)
        ·
          refine ⟨4318397357097212645754197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11515726285592567055344525 4318397357097212645754197)
          ·
            refine ⟨3162888689280185043277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 4318397357097212645754197 3162888689280185043277)
            ·
              rfl

theorem cell23_1496808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 12].length) (baseStart_1496808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1496808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1496808 prefixEnd_1496808 := by exact prefixLift 1496808
  have htrace : WordTrace (prefixWord ++ tailWord_1496808) baseStart_1496808 baseEnd_1496808 := by
    simpa [prefixWord, tailWord_1496808, baseEnd_1496808] using wordTrace_append hprefix tailTrace_1496808
  have hstable : (prefixWord ++ tailWord_1496808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1496808).length < 2 ^ (prefixWord ++ tailWord_1496808).sum := by decide
  have hdescent : baseEnd_1496808 < baseStart_1496808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1496808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
