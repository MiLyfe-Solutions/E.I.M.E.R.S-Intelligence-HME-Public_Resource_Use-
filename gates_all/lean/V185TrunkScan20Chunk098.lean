import V185TrunkScan20Chunk097

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_595211 : List Nat := [1, 1, 1, 1, 5, 3, 1, 5, 2]
def baseStart_595211 : Nat := 118140960795 + 595211 * 2 ^ 59
def prefixEnd_595211 : Nat := 4983230072969 + 3 ^ 40 * 595211 * 2
def baseEnd_595211 : Nat := 271670518971889749266827

theorem tailTrace_595211 : CollatzResearch.WordTrace tailWord_595211 prefixEnd_595211 271670518971889749266827 := by
  unfold tailWord_595211
  simp only [CollatzResearch.WordTrace]
  refine ⟨21709128646659675790825487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14472752431106450527216991 21709128646659675790825487)
  ·
    refine ⟨32563692969989513686238231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21709128646659675790825487 32563692969989513686238231)
    ·
      refine ⟨48845539454984270529357347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32563692969989513686238231 48845539454984270529357347)
      ·
        refine ⟨73268309182476405794036021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48845539454984270529357347 73268309182476405794036021)
        ·
          refine ⟨6868903985857163043190877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 73268309182476405794036021 6868903985857163043190877)
          ·
            refine ⟨2575838994696436141196579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6868903985857163043190877 2575838994696436141196579)
            ·
              refine ⟨3863758492044654211794869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2575838994696436141196579 3863758492044654211794869)
              ·
                refine ⟨362227358629186332355769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3863758492044654211794869 362227358629186332355769)
                ·
                  refine ⟨271670518971889749266827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 362227358629186332355769 271670518971889749266827)
                  ·
                    rfl

theorem cell20_595211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 5, 2].length) (baseStart_595211 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_595211 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_595211 prefixEnd_595211 := by exact prefixLift 595211
  have htrace : WordTrace (prefixWord ++ tailWord_595211) baseStart_595211 baseEnd_595211 := by
    simpa [prefixWord, tailWord_595211, baseEnd_595211] using wordTrace_append hprefix tailTrace_595211
  have hstable : (prefixWord ++ tailWord_595211).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595211).length < 2 ^ (prefixWord ++ tailWord_595211).sum := by decide
  have hdescent : baseEnd_595211 < baseStart_595211 := by decide
  rcases family_descends (prefixWord ++ tailWord_595211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595287 : List Nat := [1, 1, 3, 2, 3, 4, 1, 1, 4]
def baseStart_595287 : Nat := 118140960795 + 595287 * 2 ^ 59
def prefixEnd_595287 : Nat := 4983230072969 + 3 ^ 40 * 595287 * 2
def baseEnd_595287 : Nat := 271705207442771262733183

theorem tailTrace_595287 : CollatzResearch.WordTrace tailWord_595287 prefixEnd_595287 271705207442771262733183 := by
  unfold tailWord_595287
  simp only [CollatzResearch.WordTrace]
  refine ⟨21711900594384340770592115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14474600396256227180394743 21711900594384340770592115)
  ·
    refine ⟨32567850891576511155888173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21711900594384340770592115 32567850891576511155888173)
    ·
      refine ⟨12212944084341191683458065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32567850891576511155888173 12212944084341191683458065)
      ·
        refine ⟨9159708063255893762593549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12212944084341191683458065 9159708063255893762593549)
        ·
          refine ⟨3434890523720960160972581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9159708063255893762593549 3434890523720960160972581)
          ·
            refine ⟨644041973197680030182359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3434890523720960160972581 644041973197680030182359)
            ·
              refine ⟨966062959796520045273539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 644041973197680030182359 966062959796520045273539)
              ·
                refine ⟨1449094439694780067910309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 966062959796520045273539 1449094439694780067910309)
                ·
                  refine ⟨271705207442771262733183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1449094439694780067910309 271705207442771262733183)
                  ·
                    rfl

theorem cell20_595287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 1, 4].length) (baseStart_595287 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_595287 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_595287 prefixEnd_595287 := by exact prefixLift 595287
  have htrace : WordTrace (prefixWord ++ tailWord_595287) baseStart_595287 baseEnd_595287 := by
    simpa [prefixWord, tailWord_595287, baseEnd_595287] using wordTrace_append hprefix tailTrace_595287
  have hstable : (prefixWord ++ tailWord_595287).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595287).length < 2 ^ (prefixWord ++ tailWord_595287).sum := by decide
  have hdescent : baseEnd_595287 < baseStart_595287 := by decide
  rcases family_descends (prefixWord ++ tailWord_595287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595301 : List Nat := [1, 3, 1, 3, 1, 2, 3, 3, 3]
def baseStart_595301 : Nat := 118140960795 + 595301 * 2 ^ 59
def prefixEnd_595301 : Nat := 4983230072969 + 3 ^ 40 * 595301 * 2
def baseEnd_595301 : Nat := 271711597424249436266459

theorem tailTrace_595301 : CollatzResearch.WordTrace tailWord_595301 prefixEnd_595301 271711597424249436266459 := by
  unfold tailWord_595301
  simp only [CollatzResearch.WordTrace]
  refine ⟨21712411216333621161601757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14474940810889080774401171 21712411216333621161601757)
  ·
    refine ⟨8142154206125107935600659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21712411216333621161601757 8142154206125107935600659)
    ·
      refine ⟨12213231309187661903400989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8142154206125107935600659 12213231309187661903400989)
      ·
        refine ⟨4579961740945373213775371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12213231309187661903400989 4579961740945373213775371)
        ·
          refine ⟨6869942611418059820663057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4579961740945373213775371 6869942611418059820663057)
          ·
            refine ⟨5152456958563544865497293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6869942611418059820663057 5152456958563544865497293)
            ·
              refine ⟨1932171359461329324561485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5152456958563544865497293 1932171359461329324561485)
              ·
                refine ⟨724564259797998496710557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1932171359461329324561485 724564259797998496710557)
                ·
                  refine ⟨271711597424249436266459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 724564259797998496710557 271711597424249436266459)
                  ·
                    rfl

theorem cell20_595301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 3, 3].length) (baseStart_595301 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_595301 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_595301 prefixEnd_595301 := by exact prefixLift 595301
  have htrace : WordTrace (prefixWord ++ tailWord_595301) baseStart_595301 baseEnd_595301 := by
    simpa [prefixWord, tailWord_595301, baseEnd_595301] using wordTrace_append hprefix tailTrace_595301
  have hstable : (prefixWord ++ tailWord_595301).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595301).length < 2 ^ (prefixWord ++ tailWord_595301).sum := by decide
  have hdescent : baseEnd_595301 < baseStart_595301 := by decide
  rcases family_descends (prefixWord ++ tailWord_595301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595325 : List Nat := [1, 4, 1, 1, 2, 2, 2, 5, 2]
def baseStart_595325 : Nat := 118140960795 + 595325 * 2 ^ 59
def prefixEnd_595325 : Nat := 4983230072969 + 3 ^ 40 * 595325 * 2
def baseEnd_595325 : Nat := 271722551678212019466361

theorem tailTrace_595325 : CollatzResearch.WordTrace tailWord_595325 prefixEnd_595325 271722551678212019466361 := by
  unfold tailWord_595325
  simp only [CollatzResearch.WordTrace]
  refine ⟨21713286568246673260475429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14475524378831115506983619 21713286568246673260475429)
  ·
    refine ⟨4071241231546251236339143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21713286568246673260475429 4071241231546251236339143)
    ·
      refine ⟨6106861847319376854508715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4071241231546251236339143 6106861847319376854508715)
      ·
        refine ⟨9160292770979065281763073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6106861847319376854508715 9160292770979065281763073)
        ·
          refine ⟨6870219578234298961322305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9160292770979065281763073 6870219578234298961322305)
          ·
            refine ⟨5152664683675724220991729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6870219578234298961322305 5152664683675724220991729)
            ·
              refine ⟨3864498512756793165743797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5152664683675724220991729 3864498512756793165743797)
              ·
                refine ⟨362296735570949359288481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3864498512756793165743797 362296735570949359288481)
                ·
                  refine ⟨271722551678212019466361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 362296735570949359288481 271722551678212019466361)
                  ·
                    rfl

theorem cell20_595325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 5, 2].length) (baseStart_595325 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_595325 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_595325 prefixEnd_595325 := by exact prefixLift 595325
  have htrace : WordTrace (prefixWord ++ tailWord_595325) baseStart_595325 baseEnd_595325 := by
    simpa [prefixWord, tailWord_595325, baseEnd_595325] using wordTrace_append hprefix tailTrace_595325
  have hstable : (prefixWord ++ tailWord_595325).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595325).length < 2 ^ (prefixWord ++ tailWord_595325).sum := by decide
  have hdescent : baseEnd_595325 < baseStart_595325 := by decide
  rcases family_descends (prefixWord ++ tailWord_595325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595339 : List Nat := [1, 1, 1, 1, 4, 3, 4, 2, 3]
def baseStart_595339 : Nat := 118140960795 + 595339 * 2 ^ 59
def prefixEnd_595339 : Nat := 4983230072969 + 3 ^ 40 * 595339 * 2
def baseEnd_595339 : Nat := 271728941659690192999637

theorem tailTrace_595339 : CollatzResearch.WordTrace tailWord_595339 prefixEnd_595339 271728941659690192999637 := by
  unfold tailWord_595339
  simp only [CollatzResearch.WordTrace]
  refine ⟨21713797190195953651485071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14475864793463969100990047 21713797190195953651485071)
  ·
    refine ⟨32570695785293930477227607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21713797190195953651485071 32570695785293930477227607)
    ·
      refine ⟨48856043677940895715841411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32570695785293930477227607 48856043677940895715841411)
      ·
        refine ⟨73284065516911343573762117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48856043677940895715841411 73284065516911343573762117)
        ·
          refine ⟨13740762284420876920080397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73284065516911343573762117 13740762284420876920080397)
          ·
            refine ⟨5152785856657828845030149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13740762284420876920080397 5152785856657828845030149)
            ·
              refine ⟨966147348123342908443153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5152785856657828845030149 966147348123342908443153)
              ·
                refine ⟨724610511092507181332365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 966147348123342908443153 724610511092507181332365)
                ·
                  refine ⟨271728941659690192999637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 724610511092507181332365 271728941659690192999637)
                  ·
                    rfl

theorem cell20_595339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 2, 3].length) (baseStart_595339 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_595339 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_595339 prefixEnd_595339 := by exact prefixLift 595339
  have htrace : WordTrace (prefixWord ++ tailWord_595339) baseStart_595339 baseEnd_595339 := by
    simpa [prefixWord, tailWord_595339, baseEnd_595339] using wordTrace_append hprefix tailTrace_595339
  have hstable : (prefixWord ++ tailWord_595339).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595339).length < 2 ^ (prefixWord ++ tailWord_595339).sum := by decide
  have hdescent : baseEnd_595339 < baseStart_595339 := by decide
  rcases family_descends (prefixWord ++ tailWord_595339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595353 : List Nat := [1, 2, 1, 2, 1, 5, 3, 5]
def baseStart_595353 : Nat := 118140960795 + 595353 * 2 ^ 59
def prefixEnd_595353 : Nat := 4983230072969 + 3 ^ 40 * 595353 * 2
def baseEnd_595353 : Nat := 90578443880389455510971

theorem tailTrace_595353 : CollatzResearch.WordTrace tailWord_595353 prefixEnd_595353 90578443880389455510971 := by
  unfold tailWord_595353
  simp only [CollatzResearch.WordTrace]
  refine ⟨21714307812145234042494713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14476205208096822694996475 21714307812145234042494713)
  ·
    refine ⟨16285730859108925531871035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21714307812145234042494713 16285730859108925531871035)
    ·
      refine ⟨24428596288663388297806553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16285730859108925531871035 24428596288663388297806553)
      ·
        refine ⟨18321447216497541223354915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24428596288663388297806553 18321447216497541223354915)
        ·
          refine ⟨27482170824746311835032373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18321447216497541223354915 27482170824746311835032373)
          ·
            refine ⟨2576453514819966734534285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27482170824746311835032373 2576453514819966734534285)
            ·
              refine ⟨966170068057487525450357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2576453514819966734534285 966170068057487525450357)
              ·
                refine ⟨90578443880389455510971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 966170068057487525450357 90578443880389455510971)
                ·
                  rfl

theorem cell20_595353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 5].length) (baseStart_595353 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_595353 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_595353 prefixEnd_595353 := by exact prefixLift 595353
  have htrace : WordTrace (prefixWord ++ tailWord_595353) baseStart_595353 baseEnd_595353 := by
    simpa [prefixWord, tailWord_595353, baseEnd_595353] using wordTrace_append hprefix tailTrace_595353
  have hstable : (prefixWord ++ tailWord_595353).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595353).length < 2 ^ (prefixWord ++ tailWord_595353).sum := by decide
  have hdescent : baseEnd_595353 < baseStart_595353 := by decide
  rcases family_descends (prefixWord ++ tailWord_595353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595439 : List Nat := [1, 1, 2, 1, 4, 1, 5, 3, 2]
def baseStart_595439 : Nat := 118140960795 + 595439 * 2 ^ 59
def prefixEnd_595439 : Nat := 4983230072969 + 3 ^ 40 * 595439 * 2
def baseEnd_595439 : Nat := 271774584384534289665895

theorem tailTrace_595439 : CollatzResearch.WordTrace tailWord_595439 prefixEnd_595439 271774584384534289665895 := by
  unfold tailWord_595439
  simp only [CollatzResearch.WordTrace]
  refine ⟨21717444489833670730125371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14478296326555780486750247 21717444489833670730125371)
  ·
    refine ⟨32576166734750506095188057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21717444489833670730125371 32576166734750506095188057)
    ·
      refine ⟨24432125051062879571391043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32576166734750506095188057 24432125051062879571391043)
      ·
        refine ⟨36648187576594319357086565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24432125051062879571391043 36648187576594319357086565)
        ·
          refine ⟨6871535170611434879453731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36648187576594319357086565 6871535170611434879453731)
          ·
            refine ⟨10307302755917152319180597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6871535170611434879453731 10307302755917152319180597)
            ·
              refine ⟨966309633367233029923181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10307302755917152319180597 966309633367233029923181)
              ·
                refine ⟨362366112512712386221193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 966309633367233029923181 362366112512712386221193)
                ·
                  refine ⟨271774584384534289665895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 362366112512712386221193 271774584384534289665895)
                  ·
                    rfl

theorem cell20_595439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 3, 2].length) (baseStart_595439 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_595439 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_595439 prefixEnd_595439 := by exact prefixLift 595439
  have htrace : WordTrace (prefixWord ++ tailWord_595439) baseStart_595439 baseEnd_595439 := by
    simpa [prefixWord, tailWord_595439, baseEnd_595439] using wordTrace_append hprefix tailTrace_595439
  have hstable : (prefixWord ++ tailWord_595439).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595439).length < 2 ^ (prefixWord ++ tailWord_595439).sum := by decide
  have hdescent : baseEnd_595439 < baseStart_595439 := by decide
  rcases family_descends (prefixWord ++ tailWord_595439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595446 : List Nat := [5, 1, 1, 1, 2, 4, 6]
def baseStart_595446 : Nat := 118140960795 + 595446 * 2 ^ 59
def prefixEnd_595446 : Nat := 4983230072969 + 3 ^ 40 * 595446 * 2
def baseEnd_595446 : Nat := 30197531041697041825837

theorem tailTrace_595446 : CollatzResearch.WordTrace tailWord_595446 prefixEnd_595446 30197531041697041825837 := by
  unfold tailWord_595446
  simp only [CollatzResearch.WordTrace]
  refine ⟨1357356237550519432851887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14478466533872207283753461 1357356237550519432851887)
  ·
    refine ⟨2036034356325779149277831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1357356237550519432851887 2036034356325779149277831)
    ·
      refine ⟨3054051534488668723916747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2036034356325779149277831 3054051534488668723916747)
      ·
        refine ⟨4581077301733003085875121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3054051534488668723916747 4581077301733003085875121)
        ·
          refine ⟨3435807976299752314406341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4581077301733003085875121 3435807976299752314406341)
          ·
            refine ⟨644213995556203558951189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3435807976299752314406341 644213995556203558951189)
            ·
              refine ⟨30197531041697041825837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 644213995556203558951189 30197531041697041825837)
              ·
                rfl

theorem cell20_595446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 6].length) (baseStart_595446 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_595446 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_595446 prefixEnd_595446 := by exact prefixLift 595446
  have htrace : WordTrace (prefixWord ++ tailWord_595446) baseStart_595446 baseEnd_595446 := by
    simpa [prefixWord, tailWord_595446, baseEnd_595446] using wordTrace_append hprefix tailTrace_595446
  have hstable : (prefixWord ++ tailWord_595446).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595446).length < 2 ^ (prefixWord ++ tailWord_595446).sum := by decide
  have hdescent : baseEnd_595446 < baseStart_595446 := by decide
  rcases family_descends (prefixWord ++ tailWord_595446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595462 : List Nat := [6, 2, 1, 1, 2, 2, 2, 1, 3]
def baseStart_595462 : Nat := 118140960795 + 595462 * 2 ^ 59
def prefixEnd_595462 : Nat := 4983230072969 + 3 ^ 40 * 595462 * 2
def baseEnd_595462 : Nat := 271785082211248431899135

theorem tailTrace_595462 : CollatzResearch.WordTrace tailWord_595462 prefixEnd_595462 271785082211248431899135 := by
  unfold tailWord_595462
  simp only [CollatzResearch.WordTrace]
  refine ⟨678696355273448301819145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14478855579166897105475093 678696355273448301819145)
  ·
    refine ⟨509022266455086226364359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 678696355273448301819145 509022266455086226364359)
    ·
      refine ⟨763533399682629339546539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 509022266455086226364359 763533399682629339546539)
      ·
        refine ⟨1145300099523944009319809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 763533399682629339546539 1145300099523944009319809)
        ·
          refine ⟨858975074642958006989857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1145300099523944009319809 858975074642958006989857)
          ·
            refine ⟨644231305982218505242393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 858975074642958006989857 644231305982218505242393)
            ·
              refine ⟨483173479486663878931795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 644231305982218505242393 483173479486663878931795)
              ·
                refine ⟨724760219229995818397693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 483173479486663878931795 724760219229995818397693)
                ·
                  refine ⟨271785082211248431899135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 724760219229995818397693 271785082211248431899135)
                  ·
                    rfl

theorem cell20_595462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_595462 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_595462 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_595462 prefixEnd_595462 := by exact prefixLift 595462
  have htrace : WordTrace (prefixWord ++ tailWord_595462) baseStart_595462 baseEnd_595462 := by
    simpa [prefixWord, tailWord_595462, baseEnd_595462] using wordTrace_append hprefix tailTrace_595462
  have hstable : (prefixWord ++ tailWord_595462).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595462).length < 2 ^ (prefixWord ++ tailWord_595462).sum := by decide
  have hdescent : baseEnd_595462 < baseStart_595462 := by decide
  rcases family_descends (prefixWord ++ tailWord_595462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595470 : List Nat := [4, 1, 1, 2, 4, 1, 1, 3, 3]
def baseStart_595470 : Nat := 118140960795 + 595470 * 2 ^ 59
def prefixEnd_595470 : Nat := 4983230072969 + 3 ^ 40 * 595470 * 2
def baseEnd_595470 : Nat := 271788733629235959632435

theorem tailTrace_595470 : CollatzResearch.WordTrace tailWord_595470 prefixEnd_595470 271788733629235959632435 := by
  unfold tailWord_595470
  simp only [CollatzResearch.WordTrace]
  refine ⟨2714821894090170378062983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14479050101814242016335909 2714821894090170378062983)
  ·
    refine ⟨4072232841135255567094475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2714821894090170378062983 4072232841135255567094475)
    ·
      refine ⟨6108349261702883350641713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4072232841135255567094475 6108349261702883350641713)
      ·
        refine ⟨4581261946277162512981285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6108349261702883350641713 4581261946277162512981285)
        ·
          refine ⟨858986614926967971183991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4581261946277162512981285 858986614926967971183991)
          ·
            refine ⟨1288479922390451956775987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 858986614926967971183991 1288479922390451956775987)
            ·
              refine ⟨1932719883585677935163981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1288479922390451956775987 1932719883585677935163981)
              ·
                refine ⟨724769956344629225686493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1932719883585677935163981 724769956344629225686493)
                ·
                  refine ⟨271788733629235959632435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 724769956344629225686493 271788733629235959632435)
                  ·
                    rfl

theorem cell20_595470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 3, 3].length) (baseStart_595470 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_595470 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_595470 prefixEnd_595470 := by exact prefixLift 595470
  have htrace : WordTrace (prefixWord ++ tailWord_595470) baseStart_595470 baseEnd_595470 := by
    simpa [prefixWord, tailWord_595470, baseEnd_595470] using wordTrace_append hprefix tailTrace_595470
  have hstable : (prefixWord ++ tailWord_595470).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595470).length < 2 ^ (prefixWord ++ tailWord_595470).sum := by decide
  have hdescent : baseEnd_595470 < baseStart_595470 := by decide
  rcases family_descends (prefixWord ++ tailWord_595470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595553 : List Nat := [1, 2, 3, 1, 1, 3, 4, 3, 2]
def baseStart_595553 : Nat := 118140960795 + 595553 * 2 ^ 59
def prefixEnd_595553 : Nat := 4983230072969 + 3 ^ 40 * 595553 * 2
def baseEnd_595553 : Nat := 271826617090856559865429

theorem tailTrace_595553 : CollatzResearch.WordTrace tailWord_595553 prefixEnd_595553 271826617090856559865429 := by
  unfold tailWord_595553
  simp only [CollatzResearch.WordTrace]
  refine ⟨21721602411420668199775313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14481068274280445466516875 21721602411420668199775313)
  ·
    refine ⟨16291201808565501149831485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21721602411420668199775313 16291201808565501149831485)
    ·
      refine ⟨6109200678212062931186807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16291201808565501149831485 6109200678212062931186807)
      ·
        refine ⟨9163801017318094396780211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6109200678212062931186807 9163801017318094396780211)
        ·
          refine ⟨13745701525977141595170317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9163801017318094396780211 13745701525977141595170317)
          ·
            refine ⟨5154638072241428098188869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13745701525977141595170317 5154638072241428098188869)
            ·
              refine ⟨966494638545267768410413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5154638072241428098188869 966494638545267768410413)
              ·
                refine ⟨362435489454475413153905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 966494638545267768410413 362435489454475413153905)
                ·
                  refine ⟨271826617090856559865429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 362435489454475413153905 271826617090856559865429)
                  ·
                    rfl

theorem cell20_595553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 3, 2].length) (baseStart_595553 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_595553 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_595553 prefixEnd_595553 := by exact prefixLift 595553
  have htrace : WordTrace (prefixWord ++ tailWord_595553) baseStart_595553 baseEnd_595553 := by
    simpa [prefixWord, tailWord_595553, baseEnd_595553] using wordTrace_append hprefix tailTrace_595553
  have hstable : (prefixWord ++ tailWord_595553).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595553).length < 2 ^ (prefixWord ++ tailWord_595553).sum := by decide
  have hdescent : baseEnd_595553 < baseStart_595553 := by decide
  rcases family_descends (prefixWord ++ tailWord_595553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595595 : List Nat := [1, 1, 1, 1, 4, 1, 3, 4, 4]
def baseStart_595595 : Nat := 118140960795 + 595595 * 2 ^ 59
def prefixEnd_595595 : Nat := 4983230072969 + 3 ^ 40 * 595595 * 2
def baseEnd_595595 : Nat := 271845787035291080465257

theorem tailTrace_595595 : CollatzResearch.WordTrace tailWord_595595 prefixEnd_595595 271845787035291080465257 := by
  unfold tailWord_595595
  simp only [CollatzResearch.WordTrace]
  refine ⟨21723134277268509372804239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14482089518179006248536159 21723134277268509372804239)
  ·
    refine ⟨32584701415902764059206359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21723134277268509372804239 32584701415902764059206359)
    ·
      refine ⟨48877052123854146088809539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32584701415902764059206359 48877052123854146088809539)
      ·
        refine ⟨73315578185781219133214309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48877052123854146088809539 73315578185781219133214309)
        ·
          refine ⟨13746670909833978587477683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73315578185781219133214309 13746670909833978587477683)
          ·
            refine ⟨20620006364750967881216525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13746670909833978587477683 20620006364750967881216525)
            ·
              refine ⟨7732502386781612955456197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20620006364750967881216525 7732502386781612955456197)
              ·
                refine ⟨1449844197521552429148037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7732502386781612955456197 1449844197521552429148037)
                ·
                  refine ⟨271845787035291080465257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1449844197521552429148037 271845787035291080465257)
                  ·
                    rfl

theorem cell20_595595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 4, 4].length) (baseStart_595595 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_595595 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_595595 prefixEnd_595595 := by exact prefixLift 595595
  have htrace : WordTrace (prefixWord ++ tailWord_595595) baseStart_595595 baseEnd_595595 := by
    simpa [prefixWord, tailWord_595595, baseEnd_595595] using wordTrace_append hprefix tailTrace_595595
  have hstable : (prefixWord ++ tailWord_595595).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595595).length < 2 ^ (prefixWord ++ tailWord_595595).sum := by decide
  have hdescent : baseEnd_595595 < baseStart_595595 := by decide
  rcases family_descends (prefixWord ++ tailWord_595595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595598 : List Nat := [4, 1, 1, 3, 1, 2, 4, 4]
def baseStart_595598 : Nat := 118140960795 + 595598 * 2 ^ 59
def prefixEnd_595598 : Nat := 4983230072969 + 3 ^ 40 * 595598 * 2
def baseEnd_595598 : Nat := 90615718772345467788415

theorem tailTrace_595598 : CollatzResearch.WordTrace tailWord_595598 prefixEnd_595598 90615718772345467788415 := by
  unfold tailWord_595598
  simp only [CollatzResearch.WordTrace]
  refine ⟨2715405462032205110645431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14482162464171760590108965 2715405462032205110645431)
  ·
    refine ⟨4073108193048307665968147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2715405462032205110645431 4073108193048307665968147)
    ·
      refine ⟨6109662289572461498952221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4073108193048307665968147 6109662289572461498952221)
      ·
        refine ⟨2291123358589673062107083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6109662289572461498952221 2291123358589673062107083)
        ·
          refine ⟨3436685037884509593160625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2291123358589673062107083 3436685037884509593160625)
          ·
            refine ⟨2577513778413382194870469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3436685037884509593160625 2577513778413382194870469)
            ·
              refine ⟨483283833452509161538213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2577513778413382194870469 483283833452509161538213)
              ·
                refine ⟨90615718772345467788415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 483283833452509161538213 90615718772345467788415)
                ·
                  rfl

theorem cell20_595598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 4, 4].length) (baseStart_595598 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_595598 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_595598 prefixEnd_595598 := by exact prefixLift 595598
  have htrace : WordTrace (prefixWord ++ tailWord_595598) baseStart_595598 baseEnd_595598 := by
    simpa [prefixWord, tailWord_595598, baseEnd_595598] using wordTrace_append hprefix tailTrace_595598
  have hstable : (prefixWord ++ tailWord_595598).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595598).length < 2 ^ (prefixWord ++ tailWord_595598).sum := by decide
  have hdescent : baseEnd_595598 < baseStart_595598 := by decide
  rcases family_descends (prefixWord ++ tailWord_595598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595604 : List Nat := [2, 4, 2, 2, 3, 1, 1, 3, 2]
def baseStart_595604 : Nat := 118140960795 + 595604 * 2 ^ 59
def prefixEnd_595604 : Nat := 4983230072969 + 3 ^ 40 * 595604 * 2
def baseEnd_595604 : Nat := 271849894880527049165221

theorem tailTrace_595604 : CollatzResearch.WordTrace tailWord_595604 prefixEnd_595604 271849894880527049165221 := by
  unfold tailWord_595604
  simp only [CollatzResearch.WordTrace]
  refine ⟨10861731267117951954940933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14482308356157269273254577 10861731267117951954940933)
  ·
    refine ⟨2036574612584615991551425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10861731267117951954940933 2036574612584615991551425)
    ·
      refine ⟨1527430959438461993663569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2036574612584615991551425 1527430959438461993663569)
      ·
        refine ⟨1145573219578846495247677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1527430959438461993663569 1145573219578846495247677)
        ·
          refine ⟨429589957342067435717879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1145573219578846495247677 429589957342067435717879)
          ·
            refine ⟨644384936013101153576819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 429589957342067435717879 644384936013101153576819)
            ·
              refine ⟨966577404019651730365229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 644384936013101153576819 966577404019651730365229)
              ·
                refine ⟨362466526507369398886961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 966577404019651730365229 362466526507369398886961)
                ·
                  refine ⟨271849894880527049165221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 362466526507369398886961 271849894880527049165221)
                  ·
                    rfl

theorem cell20_595604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 3, 2].length) (baseStart_595604 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_595604 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_595604 prefixEnd_595604 := by exact prefixLift 595604
  have htrace : WordTrace (prefixWord ++ tailWord_595604) baseStart_595604 baseEnd_595604 := by
    simpa [prefixWord, tailWord_595604, baseEnd_595604] using wordTrace_append hprefix tailTrace_595604
  have hstable : (prefixWord ++ tailWord_595604).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595604).length < 2 ^ (prefixWord ++ tailWord_595604).sum := by decide
  have hdescent : baseEnd_595604 < baseStart_595604 := by decide
  rcases family_descends (prefixWord ++ tailWord_595604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595608 : List Nat := [2, 1, 2, 4, 1, 4, 1, 3, 2]
def baseStart_595608 : Nat := 118140960795 + 595608 * 2 ^ 59
def prefixEnd_595608 : Nat := 4983230072969 + 3 ^ 40 * 595608 * 2
def baseEnd_595608 : Nat := 271851720589520813031871

theorem tailTrace_595608 : CollatzResearch.WordTrace tailWord_595608 prefixEnd_595608 271851720589520813031871 := by
  unfold tailWord_595608
  simp only [CollatzResearch.WordTrace]
  refine ⟨10861804213110706296513739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14482405617480941728684985 10861804213110706296513739)
  ·
    refine ⟨16292706319666059444770609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10861804213110706296513739 16292706319666059444770609)
    ·
      refine ⟨12219529739749544583577957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16292706319666059444770609 12219529739749544583577957)
      ·
        refine ⟨2291161826203039609420867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12219529739749544583577957 2291161826203039609420867)
        ·
          refine ⟨3436742739304559414131301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2291161826203039609420867 3436742739304559414131301)
          ·
            refine ⟨644389263619604890149619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3436742739304559414131301 644389263619604890149619)
            ·
              refine ⟨966583895429407335224429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 644389263619604890149619 966583895429407335224429)
              ·
                refine ⟨362468960786027750709161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 966583895429407335224429 362468960786027750709161)
                ·
                  refine ⟨271851720589520813031871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 362468960786027750709161 271851720589520813031871)
                  ·
                    rfl

theorem cell20_595608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 3, 2].length) (baseStart_595608 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_595608 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_595608 prefixEnd_595608 := by exact prefixLift 595608
  have htrace : WordTrace (prefixWord ++ tailWord_595608) baseStart_595608 baseEnd_595608 := by
    simpa [prefixWord, tailWord_595608, baseEnd_595608] using wordTrace_append hprefix tailTrace_595608
  have hstable : (prefixWord ++ tailWord_595608).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595608).length < 2 ^ (prefixWord ++ tailWord_595608).sum := by decide
  have hdescent : baseEnd_595608 < baseStart_595608 := by decide
  rcases family_descends (prefixWord ++ tailWord_595608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595615 : List Nat := [1, 1, 2, 7, 2, 1, 6]
def baseStart_595615 : Nat := 118140960795 + 595615 * 2 ^ 59
def prefixEnd_595615 : Nat := 4983230072969 + 3 ^ 40 * 595615 * 2
def baseEnd_595615 : Nat := 30206101731139988866501

theorem tailTrace_595615 : CollatzResearch.WordTrace tailWord_595615 prefixEnd_595615 30206101731139988866501 := by
  unfold tailWord_595615
  simp only [CollatzResearch.WordTrace]
  refine ⟨21723863737196052788532299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14482575824797368525688199 21723863737196052788532299)
  ·
    refine ⟨32585795605794079182798449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21723863737196052788532299 32585795605794079182798449)
    ·
      refine ⟨24439346704345559387098837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32585795605794079182798449 24439346704345559387098837)
      ·
        refine ⟨572797188383099048135129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 24439346704345559387098837 572797188383099048135129)
        ·
          refine ⟨429597891287324286101347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 572797188383099048135129 429597891287324286101347)
          ·
            refine ⟨644396836930986429152021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 429597891287324286101347 644396836930986429152021)
            ·
              refine ⟨30206101731139988866501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 644396836930986429152021 30206101731139988866501)
              ·
                rfl

theorem cell20_595615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 6].length) (baseStart_595615 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_595615 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_595615 prefixEnd_595615 := by exact prefixLift 595615
  have htrace : WordTrace (prefixWord ++ tailWord_595615) baseStart_595615 baseEnd_595615 := by
    simpa [prefixWord, tailWord_595615, baseEnd_595615] using wordTrace_append hprefix tailTrace_595615
  have hstable : (prefixWord ++ tailWord_595615).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595615).length < 2 ^ (prefixWord ++ tailWord_595615).sum := by decide
  have hdescent : baseEnd_595615 < baseStart_595615 := by decide
  rcases family_descends (prefixWord ++ tailWord_595615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595677 : List Nat := [1, 4, 3, 3, 1, 1, 2, 2, 3]
def baseStart_595677 : Nat := 118140960795 + 595677 * 2 ^ 59
def prefixEnd_595677 : Nat := 4983230072969 + 3 ^ 40 * 595677 * 2
def baseEnd_595677 : Nat := 271883214069663239731589

theorem tailTrace_595677 : CollatzResearch.WordTrace tailWord_595677 prefixEnd_595677 271883214069663239731589 := by
  unfold tailWord_595677
  simp only [CollatzResearch.WordTrace]
  refine ⟨21726125062971437377289285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14484083375314291584859523 21726125062971437377289285)
  ·
    refine ⟨4073648449307144508241741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21726125062971437377289285 4073648449307144508241741)
    ·
      refine ⟨1527618168490179190590653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4073648449307144508241741 1527618168490179190590653)
      ·
        refine ⟨572856813183817196471495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1527618168490179190590653 572856813183817196471495)
        ·
          refine ⟨859285219775725794707243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 572856813183817196471495 859285219775725794707243)
          ·
            refine ⟨1288927829663588692060865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 859285219775725794707243 1288927829663588692060865)
            ·
              refine ⟨966695872247691519045649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1288927829663588692060865 966695872247691519045649)
              ·
                refine ⟨725021904185768639284237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 966695872247691519045649 725021904185768639284237)
                ·
                  refine ⟨271883214069663239731589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 725021904185768639284237 271883214069663239731589)
                  ·
                    rfl

theorem cell20_595677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 2, 3].length) (baseStart_595677 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_595677 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_595677 prefixEnd_595677 := by exact prefixLift 595677
  have htrace : WordTrace (prefixWord ++ tailWord_595677) baseStart_595677 baseEnd_595677 := by
    simpa [prefixWord, tailWord_595677, baseEnd_595677] using wordTrace_append hprefix tailTrace_595677
  have hstable : (prefixWord ++ tailWord_595677).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595677).length < 2 ^ (prefixWord ++ tailWord_595677).sum := by decide
  have hdescent : baseEnd_595677 < baseStart_595677 := by decide
  rcases family_descends (prefixWord ++ tailWord_595677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595740 : List Nat := [2, 2, 3, 1, 1, 2, 3, 1, 5]
def baseStart_595740 : Nat := 118140960795 + 595740 * 2 ^ 59
def prefixEnd_595740 : Nat := 4983230072969 + 3 ^ 40 * 595740 * 2
def baseEnd_595740 : Nat := 271911968986315020631331

theorem tailTrace_595740 : CollatzResearch.WordTrace tailWord_595740 prefixEnd_595740 271911968986315020631331 := by
  unfold tailWord_595740
  simp only [CollatzResearch.WordTrace]
  refine ⟨10864211430871599568416337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14485615241162132757888449 10864211430871599568416337)
  ·
    refine ⟨8148158573153699676312253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10864211430871599568416337 8148158573153699676312253)
    ·
      refine ⟨3055559464932637378617095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8148158573153699676312253 3055559464932637378617095)
      ·
        refine ⟨4583339197398956067925643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3055559464932637378617095 4583339197398956067925643)
        ·
          refine ⟨6875008796098434101888465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4583339197398956067925643 6875008796098434101888465)
          ·
            refine ⟨5156256597073825576416349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6875008796098434101888465 5156256597073825576416349)
            ·
              refine ⟨1933596223902684591156131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5156256597073825576416349 1933596223902684591156131)
              ·
                refine ⟨2900394335854026886734197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1933596223902684591156131 2900394335854026886734197)
                ·
                  refine ⟨271911968986315020631331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2900394335854026886734197 271911968986315020631331)
                  ·
                    rfl

theorem cell20_595740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 5].length) (baseStart_595740 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_595740 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_595740 prefixEnd_595740 := by exact prefixLift 595740
  have htrace : WordTrace (prefixWord ++ tailWord_595740) baseStart_595740 baseEnd_595740 := by
    simpa [prefixWord, tailWord_595740, baseEnd_595740] using wordTrace_append hprefix tailTrace_595740
  have hstable : (prefixWord ++ tailWord_595740).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595740).length < 2 ^ (prefixWord ++ tailWord_595740).sum := by decide
  have hdescent : baseEnd_595740 < baseStart_595740 := by decide
  rcases family_descends (prefixWord ++ tailWord_595740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595747 : List Nat := [1, 1, 1, 4, 2, 1, 3, 3, 4]
def baseStart_595747 : Nat := 118140960795 + 595747 * 2 ^ 59
def prefixEnd_595747 : Nat := 4983230072969 + 3 ^ 40 * 595747 * 2
def baseEnd_595747 : Nat := 271915163977054107397969

theorem tailTrace_595747 : CollatzResearch.WordTrace tailWord_595747 prefixEnd_595747 271915163977054107397969 := by
  unfold tailWord_595747
  simp only [CollatzResearch.WordTrace]
  refine ⟨21728678172717839332337495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14485785448478559554891663 21728678172717839332337495)
  ·
    refine ⟨32593017259076758998506243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21728678172717839332337495 32593017259076758998506243)
    ·
      refine ⟨48889525888615138497759365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32593017259076758998506243 48889525888615138497759365)
      ·
        refine ⟨9166786104115338468329881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48889525888615138497759365 9166786104115338468329881)
        ·
          refine ⟨6875089578086503851247411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9166786104115338468329881 6875089578086503851247411)
          ·
            refine ⟨10312634367129755776871117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6875089578086503851247411 10312634367129755776871117)
            ·
              refine ⟨3867237887673658416326669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10312634367129755776871117 3867237887673658416326669)
              ·
                refine ⟨1450214207877621906122501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3867237887673658416326669 1450214207877621906122501)
                ·
                  refine ⟨271915163977054107397969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1450214207877621906122501 271915163977054107397969)
                  ·
                    rfl

theorem cell20_595747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 3, 4].length) (baseStart_595747 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_595747 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_595747 prefixEnd_595747 := by exact prefixLift 595747
  have htrace : WordTrace (prefixWord ++ tailWord_595747) baseStart_595747 baseEnd_595747 := by
    simpa [prefixWord, tailWord_595747, baseEnd_595747] using wordTrace_append hprefix tailTrace_595747
  have hstable : (prefixWord ++ tailWord_595747).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595747).length < 2 ^ (prefixWord ++ tailWord_595747).sum := by decide
  have hdescent : baseEnd_595747 < baseStart_595747 := by decide
  rcases family_descends (prefixWord ++ tailWord_595747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595788 : List Nat := [2, 2, 1, 3, 5, 1, 6]
def baseStart_595788 : Nat := 118140960795 + 595788 * 2 ^ 59
def prefixEnd_595788 : Nat := 4983230072969 + 3 ^ 40 * 595788 * 2
def baseEnd_595788 : Nat := 30214875277137798559015

theorem tailTrace_595788 : CollatzResearch.WordTrace tailWord_595788 prefixEnd_595788 30214875277137798559015 := by
  unfold tailWord_595788
  simp only [CollatzResearch.WordTrace]
  refine ⟨10865086782784651667290009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14486782377046202223053345 10865086782784651667290009)
  ·
    refine ⟨8148815087088488750467507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10865086782784651667290009 8148815087088488750467507)
    ·
      refine ⟨12223222630632733125701261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8148815087088488750467507 12223222630632733125701261)
      ·
        refine ⟨4583708486487274922137973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12223222630632733125701261 4583708486487274922137973)
        ·
          refine ⟨429722670608182023950435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4583708486487274922137973 429722670608182023950435)
          ·
            refine ⟨644584005912273035925653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 429722670608182023950435 644584005912273035925653)
            ·
              refine ⟨30214875277137798559015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 644584005912273035925653 30214875277137798559015)
              ·
                rfl

theorem cell20_595788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 6].length) (baseStart_595788 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_595788 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_595788 prefixEnd_595788 := by exact prefixLift 595788
  have htrace : WordTrace (prefixWord ++ tailWord_595788) baseStart_595788 baseEnd_595788 := by
    simpa [prefixWord, tailWord_595788, baseEnd_595788] using wordTrace_append hprefix tailTrace_595788
  have hstable : (prefixWord ++ tailWord_595788).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595788).length < 2 ^ (prefixWord ++ tailWord_595788).sum := by decide
  have hdescent : baseEnd_595788 < baseStart_595788 := by decide
  rcases family_descends (prefixWord ++ tailWord_595788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595840 : List Nat := [2, 1, 1, 2, 1, 2, 4, 5, 2]
def baseStart_595840 : Nat := 118140960795 + 595840 * 2 ^ 59
def prefixEnd_595840 : Nat := 4983230072969 + 3 ^ 40 * 595840 * 2
def baseEnd_595840 : Nat := 271957611711159117297589

theorem tailTrace_595840 : CollatzResearch.WordTrace tailWord_595840 prefixEnd_595840 271957611711159117297589 := by
  unfold tailWord_595840
  simp only [CollatzResearch.WordTrace]
  refine ⟨10866035080690458107736487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14488046774253944143648649 10866035080690458107736487)
  ·
    refine ⟨16299052621035687161604731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10866035080690458107736487 16299052621035687161604731)
    ·
      refine ⟨24448578931553530742407097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16299052621035687161604731 24448578931553530742407097)
      ·
        refine ⟨18336434198665148056805323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24448578931553530742407097 18336434198665148056805323)
        ·
          refine ⟨27504651297997722085207985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18336434198665148056805323 27504651297997722085207985)
          ·
            refine ⟨20628488473498291563905989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27504651297997722085207985 20628488473498291563905989)
            ·
              refine ⟨3867841588780929668232373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20628488473498291563905989 3867841588780929668232373)
              ·
                refine ⟨362610148948212156396785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3867841588780929668232373 362610148948212156396785)
                ·
                  refine ⟨271957611711159117297589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 362610148948212156396785 271957611711159117297589)
                  ·
                    rfl

theorem cell20_595840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 5, 2].length) (baseStart_595840 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_595840 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_595840 prefixEnd_595840 := by exact prefixLift 595840
  have htrace : WordTrace (prefixWord ++ tailWord_595840) baseStart_595840 baseEnd_595840 := by
    simpa [prefixWord, tailWord_595840, baseEnd_595840] using wordTrace_append hprefix tailTrace_595840
  have hstable : (prefixWord ++ tailWord_595840).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595840).length < 2 ^ (prefixWord ++ tailWord_595840).sum := by decide
  have hdescent : baseEnd_595840 < baseStart_595840 := by decide
  rcases family_descends (prefixWord ++ tailWord_595840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595847 : List Nat := [1, 1, 4, 2, 5, 7]
def baseStart_595847 : Nat := 118140960795 + 595847 * 2 ^ 59
def prefixEnd_595847 : Nat := 4983230072969 + 3 ^ 40 * 595847 * 2
def baseEnd_595847 : Nat := 10072622470440674224601

theorem tailTrace_595847 : CollatzResearch.WordTrace tailWord_595847 prefixEnd_595847 10072622470440674224601 := by
  unfold tailWord_595847
  simp only [CollatzResearch.WordTrace]
  refine ⟨21732325472355556410977795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14488216981570370940651863 21732325472355556410977795)
  ·
    refine ⟨32598488208533334616466693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21732325472355556410977795 32598488208533334616466693)
    ·
      refine ⟨6112216539100000240587505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32598488208533334616466693 6112216539100000240587505)
      ·
        refine ⟨4584162404325000180440629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6112216539100000240587505 4584162404325000180440629)
        ·
          refine ⟨429765225405468766916309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4584162404325000180440629 429765225405468766916309)
          ·
            refine ⟨10072622470440674224601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 429765225405468766916309 10072622470440674224601)
            ·
              rfl

theorem cell20_595847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 7].length) (baseStart_595847 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_595847 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_595847 prefixEnd_595847 := by exact prefixLift 595847
  have htrace : WordTrace (prefixWord ++ tailWord_595847) baseStart_595847 baseEnd_595847 := by
    simpa [prefixWord, tailWord_595847, baseEnd_595847] using wordTrace_append hprefix tailTrace_595847
  have hstable : (prefixWord ++ tailWord_595847).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595847).length < 2 ^ (prefixWord ++ tailWord_595847).sum := by decide
  have hdescent : baseEnd_595847 < baseStart_595847 := by decide
  rcases family_descends (prefixWord ++ tailWord_595847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595850 : List Nat := [3, 1, 2, 4, 2, 1, 2, 2, 3]
def baseStart_595850 : Nat := 118140960795 + 595850 * 2 ^ 59
def prefixEnd_595850 : Nat := 4983230072969 + 3 ^ 40 * 595850 * 2
def baseEnd_595850 : Nat := 271962175983643526964215

theorem tailTrace_595850 : CollatzResearch.WordTrace tailWord_595850 prefixEnd_595850 271962175983643526964215 := by
  unfold tailWord_595850
  simp only [CollatzResearch.WordTrace]
  refine ⟨5433108722836171980834251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14488289927563125282224669 5433108722836171980834251)
  ·
    refine ⟨8149663084254257971251377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5433108722836171980834251 8149663084254257971251377)
    ·
      refine ⟨6112247313190693478438533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8149663084254257971251377 6112247313190693478438533)
      ·
        refine ⟨1146046371223255027207225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6112247313190693478438533 1146046371223255027207225)
        ·
          refine ⟨859534778417441270405419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1146046371223255027207225 859534778417441270405419)
          ·
            refine ⟨1289302167626161905608129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 859534778417441270405419 1289302167626161905608129)
            ·
              refine ⟨966976625719621429206097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1289302167626161905608129 966976625719621429206097)
              ·
                refine ⟨725232469289716071904573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 966976625719621429206097 725232469289716071904573)
                ·
                  refine ⟨271962175983643526964215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 725232469289716071904573 271962175983643526964215)
                  ·
                    rfl

theorem cell20_595850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 2, 3].length) (baseStart_595850 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_595850 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_595850 prefixEnd_595850 := by exact prefixLift 595850
  have htrace : WordTrace (prefixWord ++ tailWord_595850) baseStart_595850 baseEnd_595850 := by
    simpa [prefixWord, tailWord_595850, baseEnd_595850] using wordTrace_append hprefix tailTrace_595850
  have hstable : (prefixWord ++ tailWord_595850).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595850).length < 2 ^ (prefixWord ++ tailWord_595850).sum := by decide
  have hdescent : baseEnd_595850 < baseStart_595850 := by decide
  rcases family_descends (prefixWord ++ tailWord_595850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595857 : List Nat := [1, 2, 2, 1, 1, 1, 8, 2, 2]
def baseStart_595857 : Nat := 118140960795 + 595857 * 2 ^ 59
def prefixEnd_595857 : Nat := 4983230072969 + 3 ^ 40 * 595857 * 2
def baseEnd_595857 : Nat := 271965370974382613730853

theorem tailTrace_595857 : CollatzResearch.WordTrace tailWord_595857 prefixEnd_595857 271965370974382613730853 := by
  unfold tailWord_595857
  simp only [CollatzResearch.WordTrace]
  refine ⟨21732690202319328118841825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14488460134879552079227883 21732690202319328118841825)
  ·
    refine ⟨16299517651739496089131369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21732690202319328118841825 16299517651739496089131369)
    ·
      refine ⟨12224638238804622066848527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16299517651739496089131369 12224638238804622066848527)
      ·
        refine ⟨18336957358206933100272791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12224638238804622066848527 18336957358206933100272791)
        ·
          refine ⟨27505436037310399650409187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18336957358206933100272791 27505436037310399650409187)
          ·
            refine ⟨41258154055965599475613781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27505436037310399650409187 41258154055965599475613781)
            ·
              refine ⟨483493992843346868854849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 41258154055965599475613781 483493992843346868854849)
              ·
                refine ⟨362620494632510151641137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 483493992843346868854849 362620494632510151641137)
                ·
                  refine ⟨271965370974382613730853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 362620494632510151641137 271965370974382613730853)
                  ·
                    rfl

theorem cell20_595857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 8, 2, 2].length) (baseStart_595857 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_595857 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_595857 prefixEnd_595857 := by exact prefixLift 595857
  have htrace : WordTrace (prefixWord ++ tailWord_595857) baseStart_595857 baseEnd_595857 := by
    simpa [prefixWord, tailWord_595857, baseEnd_595857] using wordTrace_append hprefix tailTrace_595857
  have hstable : (prefixWord ++ tailWord_595857).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595857).length < 2 ^ (prefixWord ++ tailWord_595857).sum := by decide
  have hdescent : baseEnd_595857 < baseStart_595857 := by decide
  rcases family_descends (prefixWord ++ tailWord_595857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595861 : List Nat := [1, 3, 2, 1, 1, 3, 2, 3, 4]
def baseStart_595861 : Nat := 118140960795 + 595861 * 2 ^ 59
def prefixEnd_595861 : Nat := 4983230072969 + 3 ^ 40 * 595861 * 2
def baseEnd_595861 : Nat := 271967196683376377597503

theorem tailTrace_595861 : CollatzResearch.WordTrace tailWord_595861 prefixEnd_595861 271967196683376377597503 := by
  unfold tailWord_595861
  simp only [CollatzResearch.WordTrace]
  refine ⟨21732836094304836801987437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14488557396203224534658291 21732836094304836801987437)
  ·
    refine ⟨8149813535364313800745289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21732836094304836801987437 8149813535364313800745289)
    ·
      refine ⟨6112360151523235350558967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8149813535364313800745289 6112360151523235350558967)
      ·
        refine ⟨9168540227284853025838451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6112360151523235350558967 9168540227284853025838451)
        ·
          refine ⟨13752810340927279538757677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9168540227284853025838451 13752810340927279538757677)
          ·
            refine ⟨5157303877847729827034129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13752810340927279538757677 5157303877847729827034129)
            ·
              refine ⟨3867977908385797370275597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5157303877847729827034129 3867977908385797370275597)
              ·
                refine ⟨1450491715644674013853349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3867977908385797370275597 1450491715644674013853349)
                ·
                  refine ⟨271967196683376377597503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1450491715644674013853349 271967196683376377597503)
                  ·
                    rfl

theorem cell20_595861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 3, 4].length) (baseStart_595861 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_595861 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_595861 prefixEnd_595861 := by exact prefixLift 595861
  have htrace : WordTrace (prefixWord ++ tailWord_595861) baseStart_595861 baseEnd_595861 := by
    simpa [prefixWord, tailWord_595861, baseEnd_595861] using wordTrace_append hprefix tailTrace_595861
  have hstable : (prefixWord ++ tailWord_595861).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595861).length < 2 ^ (prefixWord ++ tailWord_595861).sum := by decide
  have hdescent : baseEnd_595861 < baseStart_595861 := by decide
  rcases family_descends (prefixWord ++ tailWord_595861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595875 : List Nat := [1, 1, 1, 4, 1, 2, 1, 2, 7]
def baseStart_595875 : Nat := 118140960795 + 595875 * 2 ^ 59
def prefixEnd_595875 : Nat := 4983230072969 + 3 ^ 40 * 595875 * 2
def baseEnd_595875 : Nat := 271973586664854551130779

theorem tailTrace_595875 : CollatzResearch.WordTrace tailWord_595875 prefixEnd_595875 271973586664854551130779 := by
  unfold tailWord_595875
  simp only [CollatzResearch.WordTrace]
  refine ⟨21733346716254117192997079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14488897810836078128664719 21733346716254117192997079)
  ·
    refine ⟨32600020074381175789495619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21733346716254117192997079 32600020074381175789495619)
    ·
      refine ⟨48900030111571763684243429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32600020074381175789495619 48900030111571763684243429)
      ·
        refine ⟨9168755645919705690795643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48900030111571763684243429 9168755645919705690795643)
        ·
          refine ⟨13753133468879558536193465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9168755645919705690795643 13753133468879558536193465)
          ·
            refine ⟨10314850101659668902145099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13753133468879558536193465 10314850101659668902145099)
            ·
              refine ⟨15472275152489503353217649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10314850101659668902145099 15472275152489503353217649)
              ·
                refine ⟨11604206364367127514913237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15472275152489503353217649 11604206364367127514913237)
                ·
                  refine ⟨271973586664854551130779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11604206364367127514913237 271973586664854551130779)
                  ·
                    rfl

theorem cell20_595875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 7].length) (baseStart_595875 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_595875 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_595875 prefixEnd_595875 := by exact prefixLift 595875
  have htrace : WordTrace (prefixWord ++ tailWord_595875) baseStart_595875 baseEnd_595875 := by
    simpa [prefixWord, tailWord_595875, baseEnd_595875] using wordTrace_append hprefix tailTrace_595875
  have hstable : (prefixWord ++ tailWord_595875).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595875).length < 2 ^ (prefixWord ++ tailWord_595875).sum := by decide
  have hdescent : baseEnd_595875 < baseStart_595875 := by decide
  rcases family_descends (prefixWord ++ tailWord_595875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595913 : List Nat := [1, 2, 1, 1, 2, 1, 2, 5, 5]
def baseStart_595913 : Nat := 118140960795 + 595913 * 2 ^ 59
def prefixEnd_595913 : Nat := 4983230072969 + 3 ^ 40 * 595913 * 2
def baseEnd_595913 : Nat := 271990930900295307863957

theorem tailTrace_595913 : CollatzResearch.WordTrace tailWord_595913 prefixEnd_595913 271990930900295307863957 := by
  unfold tailWord_595913
  simp only [CollatzResearch.WordTrace]
  refine ⟨21734732690116449682880393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14489821793410966455253595 21734732690116449682880393)
  ·
    refine ⟨16301049517587337262160295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21734732690116449682880393 16301049517587337262160295)
    ·
      refine ⟨24451574276381005893240443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16301049517587337262160295 24451574276381005893240443)
      ·
        refine ⟨36677361414571508839860665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24451574276381005893240443 36677361414571508839860665)
        ·
          refine ⟨27508021060928631629895499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36677361414571508839860665 27508021060928631629895499)
          ·
            refine ⟨41262031591392947444843249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27508021060928631629895499 41262031591392947444843249)
            ·
              refine ⟨30946523693544710583632437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41262031591392947444843249 30946523693544710583632437)
              ·
                refine ⟨2901236596269816617215541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30946523693544710583632437 2901236596269816617215541)
                ·
                  refine ⟨271990930900295307863957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2901236596269816617215541 271990930900295307863957)
                  ·
                    rfl

theorem cell20_595913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 5].length) (baseStart_595913 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_595913 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_595913 prefixEnd_595913 := by exact prefixLift 595913
  have htrace : WordTrace (prefixWord ++ tailWord_595913) baseStart_595913 baseEnd_595913 := by
    simpa [prefixWord, tailWord_595913, baseEnd_595913] using wordTrace_append hprefix tailTrace_595913
  have hstable : (prefixWord ++ tailWord_595913).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595913).length < 2 ^ (prefixWord ++ tailWord_595913).sum := by decide
  have hdescent : baseEnd_595913 < baseStart_595913 := by decide
  rcases family_descends (prefixWord ++ tailWord_595913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595916 : List Nat := [2, 2, 1, 4, 1, 3, 2, 1, 4]
def baseStart_595916 : Nat := 118140960795 + 595916 * 2 ^ 59
def prefixEnd_595916 : Nat := 4983230072969 + 3 ^ 40 * 595916 * 2
def baseEnd_595916 : Nat := 271992300182040630763945

theorem tailTrace_595916 : CollatzResearch.WordTrace tailWord_595916 prefixEnd_595916 271992300182040630763945 := by
  unfold tailWord_595916
  simp only [CollatzResearch.WordTrace]
  refine ⟨10867421054552790597619801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14489894739403720796826401 10867421054552790597619801)
  ·
    refine ⟨8150565790914592948214851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10867421054552790597619801 8150565790914592948214851)
    ·
      refine ⟨12225848686371889422322277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8150565790914592948214851 12225848686371889422322277)
      ·
        refine ⟨2292346628694729266685427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12225848686371889422322277 2292346628694729266685427)
        ·
          refine ⟨3438519943042093900028141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2292346628694729266685427 3438519943042093900028141)
          ·
            refine ⟨1289444978640785212510553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3438519943042093900028141 1289444978640785212510553)
            ·
              refine ⟨967083733980588909382915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1289444978640785212510553 967083733980588909382915)
              ·
                refine ⟨1450625600970883364074373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 967083733980588909382915 1450625600970883364074373)
                ·
                  refine ⟨271992300182040630763945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1450625600970883364074373 271992300182040630763945)
                  ·
                    rfl

theorem cell20_595916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 1, 4].length) (baseStart_595916 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_595916 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_595916 prefixEnd_595916 := by exact prefixLift 595916
  have htrace : WordTrace (prefixWord ++ tailWord_595916) baseStart_595916 baseEnd_595916 := by
    simpa [prefixWord, tailWord_595916, baseEnd_595916] using wordTrace_append hprefix tailTrace_595916
  have hstable : (prefixWord ++ tailWord_595916).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595916).length < 2 ^ (prefixWord ++ tailWord_595916).sum := by decide
  have hdescent : baseEnd_595916 < baseStart_595916 := by decide
  rcases family_descends (prefixWord ++ tailWord_595916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595937 : List Nat := [1, 2, 3, 1, 2, 1, 4, 2, 4]
def baseStart_595937 : Nat := 118140960795 + 595937 * 2 ^ 59
def prefixEnd_595937 : Nat := 4983230072969 + 3 ^ 40 * 595937 * 2
def baseEnd_595937 : Nat := 272001885154257891063859

theorem tailTrace_595937 : CollatzResearch.WordTrace tailWord_595937 prefixEnd_595937 272001885154257891063859 := by
  unfold tailWord_595937
  simp only [CollatzResearch.WordTrace]
  refine ⟨21735608042029501781754065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14490405361353001187836043 21735608042029501781754065)
  ·
    refine ⟨16301706031522126336315549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21735608042029501781754065 16301706031522126336315549)
    ·
      refine ⟨6113139761820797376118331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16301706031522126336315549 6113139761820797376118331)
      ·
        refine ⟨9169709642731196064177497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6113139761820797376118331 9169709642731196064177497)
        ·
          refine ⟨6877282232048397048133123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9169709642731196064177497 6877282232048397048133123)
          ·
            refine ⟨10315923348072595572199685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6877282232048397048133123 10315923348072595572199685)
            ·
              refine ⟨1934235627763611669787441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10315923348072595572199685 1934235627763611669787441)
              ·
                refine ⟨1450676720822708752340581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1934235627763611669787441 1450676720822708752340581)
                ·
                  refine ⟨272001885154257891063859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1450676720822708752340581 272001885154257891063859)
                  ·
                    rfl

theorem cell20_595937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 2, 4].length) (baseStart_595937 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_595937 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_595937 prefixEnd_595937 := by exact prefixLift 595937
  have htrace : WordTrace (prefixWord ++ tailWord_595937) baseStart_595937 baseEnd_595937 := by
    simpa [prefixWord, tailWord_595937, baseEnd_595937] using wordTrace_append hprefix tailTrace_595937
  have hstable : (prefixWord ++ tailWord_595937).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595937).length < 2 ^ (prefixWord ++ tailWord_595937).sum := by decide
  have hdescent : baseEnd_595937 < baseStart_595937 := by decide
  rcases family_descends (prefixWord ++ tailWord_595937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595950 : List Nat := [4, 1, 2, 1, 3, 3, 1, 3, 2]
def baseStart_595950 : Nat := 118140960795 + 595950 * 2 ^ 59
def prefixEnd_595950 : Nat := 4983230072969 + 3 ^ 40 * 595950 * 2
def baseEnd_595950 : Nat := 272007818708487623630473

theorem tailTrace_595950 : CollatzResearch.WordTrace tailWord_595950 prefixEnd_595950 272007818708487623630473 := by
  unfold tailWord_595950
  simp only [CollatzResearch.WordTrace]
  refine ⟨2717010273872800625247163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14490721460654936667984869 2717010273872800625247163)
  ·
    refine ⟨4075515410809200937870745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2717010273872800625247163 4075515410809200937870745)
    ·
      refine ⟨3056636558106900703403059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4075515410809200937870745 3056636558106900703403059)
      ·
        refine ⟨4584954837160351055104589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3056636558106900703403059 4584954837160351055104589)
        ·
          refine ⟨1719358063935131645664221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4584954837160351055104589 1719358063935131645664221)
          ·
            refine ⟨644759273975674367124083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1719358063935131645664221 644759273975674367124083)
            ·
              refine ⟨967138910963511550686125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 644759273975674367124083 967138910963511550686125)
              ·
                refine ⟨362677091611316831507297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 967138910963511550686125 362677091611316831507297)
                ·
                  refine ⟨272007818708487623630473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 362677091611316831507297 272007818708487623630473)
                  ·
                    rfl

theorem cell20_595950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 3, 2].length) (baseStart_595950 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_595950 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_595950 prefixEnd_595950 := by exact prefixLift 595950
  have htrace : WordTrace (prefixWord ++ tailWord_595950) baseStart_595950 baseEnd_595950 := by
    simpa [prefixWord, tailWord_595950, baseEnd_595950] using wordTrace_append hprefix tailTrace_595950
  have hstable : (prefixWord ++ tailWord_595950).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595950).length < 2 ^ (prefixWord ++ tailWord_595950).sum := by decide
  have hdescent : baseEnd_595950 < baseStart_595950 := by decide
  rcases family_descends (prefixWord ++ tailWord_595950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_595951 : List Nat := [1, 1, 2, 1, 4, 2, 1, 1, 7]
def baseStart_595951 : Nat := 118140960795 + 595951 * 2 ^ 59
def prefixEnd_595951 : Nat := 4983230072969 + 3 ^ 40 * 595951 * 2
def baseEnd_595951 : Nat := 272008275135736064597135

theorem tailTrace_595951 : CollatzResearch.WordTrace tailWord_595951 prefixEnd_595951 272008275135736064597135 := by
  unfold tailWord_595951
  simp only [CollatzResearch.WordTrace]
  refine ⟨21736118663978782172763707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14490745775985854781842471 21736118663978782172763707)
  ·
    refine ⟨32604177995968173259145561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21736118663978782172763707 32604177995968173259145561)
    ·
      refine ⟨24453133496976129944359171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32604177995968173259145561 24453133496976129944359171)
      ·
        refine ⟨36679700245464194916538757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24453133496976129944359171 36679700245464194916538757)
        ·
          refine ⟨6877443796024536546851017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36679700245464194916538757 6877443796024536546851017)
          ·
            refine ⟨5158082847018402410138263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6877443796024536546851017 5158082847018402410138263)
            ·
              refine ⟨7737124270527603615207395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5158082847018402410138263 7737124270527603615207395)
              ·
                refine ⟨11605686405791405422811093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7737124270527603615207395 11605686405791405422811093)
                ·
                  refine ⟨272008275135736064597135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11605686405791405422811093 272008275135736064597135)
                  ·
                    rfl

theorem cell20_595951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 7].length) (baseStart_595951 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_595951 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_595951 prefixEnd_595951 := by exact prefixLift 595951
  have htrace : WordTrace (prefixWord ++ tailWord_595951) baseStart_595951 baseEnd_595951 := by
    simpa [prefixWord, tailWord_595951, baseEnd_595951] using wordTrace_append hprefix tailTrace_595951
  have hstable : (prefixWord ++ tailWord_595951).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_595951).length < 2 ^ (prefixWord ++ tailWord_595951).sum := by decide
  have hdescent : baseEnd_595951 < baseStart_595951 := by decide
  rcases family_descends (prefixWord ++ tailWord_595951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596044 : List Nat := [2, 2, 1, 3, 1, 1, 4, 3, 3]
def baseStart_596044 : Nat := 118140960795 + 596044 * 2 ^ 59
def prefixEnd_596044 : Nat := 4983230072969 + 3 ^ 40 * 596044 * 2
def baseEnd_596044 : Nat := 272050722869841074496755

theorem tailTrace_596044 : CollatzResearch.WordTrace tailWord_596044 prefixEnd_596044 272050722869841074496755 := by
  unfold tailWord_596044
  simp only [CollatzResearch.WordTrace]
  refine ⟨10869755326320929527949593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14493007101761239370599457 10869755326320929527949593)
  ·
    refine ⟨8152316494740697145962195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10869755326320929527949593 8152316494740697145962195)
    ·
      refine ⟨12228474742111045718943293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8152316494740697145962195 12228474742111045718943293)
      ·
        refine ⟨4585678028291642144603735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12228474742111045718943293 4585678028291642144603735)
        ·
          refine ⟨6878517042437463216905603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4585678028291642144603735 6878517042437463216905603)
          ·
            refine ⟨10317775563656194825358405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6878517042437463216905603 10317775563656194825358405)
            ·
              refine ⟨1934582918185536529754701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10317775563656194825358405 1934582918185536529754701)
              ·
                refine ⟨725468594319576198658013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1934582918185536529754701 725468594319576198658013)
                ·
                  refine ⟨272050722869841074496755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 725468594319576198658013 272050722869841074496755)
                  ·
                    rfl

theorem cell20_596044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 3, 3].length) (baseStart_596044 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_596044 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_596044 prefixEnd_596044 := by exact prefixLift 596044
  have htrace : WordTrace (prefixWord ++ tailWord_596044) baseStart_596044 baseEnd_596044 := by
    simpa [prefixWord, tailWord_596044, baseEnd_596044] using wordTrace_append hprefix tailTrace_596044
  have hstable : (prefixWord ++ tailWord_596044).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596044).length < 2 ^ (prefixWord ++ tailWord_596044).sum := by decide
  have hdescent : baseEnd_596044 < baseStart_596044 := by decide
  rcases family_descends (prefixWord ++ tailWord_596044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596065 : List Nat := [1, 2, 3, 1, 1, 2, 1, 4, 5]
def baseStart_596065 : Nat := 118140960795 + 596065 * 2 ^ 59
def prefixEnd_596065 : Nat := 4983230072969 + 3 ^ 40 * 596065 * 2
def baseEnd_596065 : Nat := 272060307842058334796669

theorem tailTrace_596065 : CollatzResearch.WordTrace tailWord_596065 prefixEnd_596065 272060307842058334796669 := by
  unfold tailWord_596065
  simp only [CollatzResearch.WordTrace]
  refine ⟨21740276585565779642413649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14493517723710519761609099 21740276585565779642413649)
  ·
    refine ⟨16305207439174334731810237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21740276585565779642413649 16305207439174334731810237)
    ·
      refine ⟨6114452789690375524428839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16305207439174334731810237 6114452789690375524428839)
      ·
        refine ⟨9171679184535563286643259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6114452789690375524428839 9171679184535563286643259)
        ·
          refine ⟨13757518776803344929964889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9171679184535563286643259 13757518776803344929964889)
          ·
            refine ⟨10318139082602508697473667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13757518776803344929964889 10318139082602508697473667)
            ·
              refine ⟨15477208623903763046210501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10318139082602508697473667 15477208623903763046210501)
              ·
                refine ⟨2901976616981955571164469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15477208623903763046210501 2901976616981955571164469)
                ·
                  refine ⟨272060307842058334796669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2901976616981955571164469 272060307842058334796669)
                  ·
                    rfl

theorem cell20_596065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 5].length) (baseStart_596065 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_596065 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_596065 prefixEnd_596065 := by exact prefixLift 596065
  have htrace : WordTrace (prefixWord ++ tailWord_596065) baseStart_596065 baseEnd_596065 := by
    simpa [prefixWord, tailWord_596065, baseEnd_596065] using wordTrace_append hprefix tailTrace_596065
  have hstable : (prefixWord ++ tailWord_596065).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596065).length < 2 ^ (prefixWord ++ tailWord_596065).sum := by decide
  have hdescent : baseEnd_596065 < baseStart_596065 := by decide
  rcases family_descends (prefixWord ++ tailWord_596065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596068 : List Nat := [2, 3, 1, 1, 2, 1, 3, 5, 2]
def baseStart_596068 : Nat := 118140960795 + 596068 * 2 ^ 59
def prefixEnd_596068 : Nat := 4983230072969 + 3 ^ 40 * 596068 * 2
def baseEnd_596068 : Nat := 272061677123803657696657

theorem tailTrace_596068 : CollatzResearch.WordTrace tailWord_596068 prefixEnd_596068 272061677123803657696657 := by
  unfold tailWord_596068
  simp only [CollatzResearch.WordTrace]
  refine ⟨10870193002277455577386429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14493590669703274103181905 10870193002277455577386429)
  ·
    refine ⟨4076322375854045841519911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10870193002277455577386429 4076322375854045841519911)
    ·
      refine ⟨6114483563781068762279867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4076322375854045841519911 6114483563781068762279867)
      ·
        refine ⟨9171725345671603143419801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6114483563781068762279867 9171725345671603143419801)
        ·
          refine ⟨6878794009253702357564851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9171725345671603143419801 6878794009253702357564851)
          ·
            refine ⟨10318191013880553536347277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6878794009253702357564851 10318191013880553536347277)
            ·
              refine ⟨3869321630205207576130229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10318191013880553536347277 3869321630205207576130229)
              ·
                refine ⟨362748902831738210262209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3869321630205207576130229 362748902831738210262209)
                ·
                  refine ⟨272061677123803657696657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 362748902831738210262209 272061677123803657696657)
                  ·
                    rfl

theorem cell20_596068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 5, 2].length) (baseStart_596068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_596068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_596068 prefixEnd_596068 := by exact prefixLift 596068
  have htrace : WordTrace (prefixWord ++ tailWord_596068) baseStart_596068 baseEnd_596068 := by
    simpa [prefixWord, tailWord_596068, baseEnd_596068] using wordTrace_append hprefix tailTrace_596068
  have hstable : (prefixWord ++ tailWord_596068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596068).length < 2 ^ (prefixWord ++ tailWord_596068).sum := by decide
  have hdescent : baseEnd_596068 < baseStart_596068 := by decide
  rcases family_descends (prefixWord ++ tailWord_596068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596082 : List Nat := [3, 2, 1, 2, 2, 3, 1, 1, 5]
def baseStart_596082 : Nat := 118140960795 + 596082 * 2 ^ 59
def prefixEnd_596082 : Nat := 4983230072969 + 3 ^ 40 * 596082 * 2
def baseEnd_596082 : Nat := 272068067105281831229933

theorem tailTrace_596082 : CollatzResearch.WordTrace tailWord_596082 prefixEnd_596082 272068067105281831229933 := by
  unfold tailWord_596082
  simp only [CollatzResearch.WordTrace]
  refine ⟨5435224156626047886445625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14493931084336127697188333 5435224156626047886445625)
  ·
    refine ⟨4076418117469535914834219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5435224156626047886445625 4076418117469535914834219)
    ·
      refine ⟨6114627176204303872251329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4076418117469535914834219 6114627176204303872251329)
      ·
        refine ⟨4585970382153227904188497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6114627176204303872251329 4585970382153227904188497)
        ·
          refine ⟨3439477786614920928141373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4585970382153227904188497 3439477786614920928141373)
          ·
            refine ⟨1289804169980595348053015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3439477786614920928141373 1289804169980595348053015)
            ·
              refine ⟨1934706254970893022079523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1289804169980595348053015 1934706254970893022079523)
              ·
                refine ⟨2902059382456339533119285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1934706254970893022079523 2902059382456339533119285)
                ·
                  refine ⟨272068067105281831229933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2902059382456339533119285 272068067105281831229933)
                  ·
                    rfl

theorem cell20_596082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_596082 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_596082 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_596082 prefixEnd_596082 := by exact prefixLift 596082
  have htrace : WordTrace (prefixWord ++ tailWord_596082) baseStart_596082 baseEnd_596082 := by
    simpa [prefixWord, tailWord_596082, baseEnd_596082] using wordTrace_append hprefix tailTrace_596082
  have hstable : (prefixWord ++ tailWord_596082).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596082).length < 2 ^ (prefixWord ++ tailWord_596082).sum := by decide
  have hdescent : baseEnd_596082 < baseStart_596082 := by decide
  rcases family_descends (prefixWord ++ tailWord_596082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596089 : List Nat := [1, 2, 1, 3, 4, 1, 1, 3, 4]
def baseStart_596089 : Nat := 118140960795 + 596089 * 2 ^ 59
def prefixEnd_596089 : Nat := 4983230072969 + 3 ^ 40 * 596089 * 2
def baseEnd_596089 : Nat := 272071262096020917996571

theorem tailTrace_596089 : CollatzResearch.WordTrace tailWord_596089 prefixEnd_596089 272071262096020917996571 := by
  unfold tailWord_596089
  simp only [CollatzResearch.WordTrace]
  refine ⟨21741151937478831741287321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14494101291652554494191547 21741151937478831741287321)
  ·
    refine ⟨16305863953109123805965491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21741151937478831741287321 16305863953109123805965491)
    ·
      refine ⟨24458795929663685708948237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16305863953109123805965491 24458795929663685708948237)
      ·
        refine ⟨9172048473623882140855589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24458795929663685708948237 9172048473623882140855589)
        ·
          refine ⟨1719759088804477901410423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9172048473623882140855589 1719759088804477901410423)
          ·
            refine ⟨2579638633206716852115635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1719759088804477901410423 2579638633206716852115635)
            ·
              refine ⟨3869457949810075278173453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2579638633206716852115635 3869457949810075278173453)
              ·
                refine ⟨1451046731178778229315045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3869457949810075278173453 1451046731178778229315045)
                ·
                  refine ⟨272071262096020917996571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1451046731178778229315045 272071262096020917996571)
                  ·
                    rfl

theorem cell20_596089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 3, 4].length) (baseStart_596089 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_596089 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_596089 prefixEnd_596089 := by exact prefixLift 596089
  have htrace : WordTrace (prefixWord ++ tailWord_596089) baseStart_596089 baseEnd_596089 := by
    simpa [prefixWord, tailWord_596089, baseEnd_596089] using wordTrace_append hprefix tailTrace_596089
  have hstable : (prefixWord ++ tailWord_596089).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596089).length < 2 ^ (prefixWord ++ tailWord_596089).sum := by decide
  have hdescent : baseEnd_596089 < baseStart_596089 := by decide
  rcases family_descends (prefixWord ++ tailWord_596089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596099 : List Nat := [1, 1, 1, 3, 3, 4, 3, 1, 3]
def baseStart_596099 : Nat := 118140960795 + 596099 * 2 ^ 59
def prefixEnd_596099 : Nat := 4983230072969 + 3 ^ 40 * 596099 * 2
def baseEnd_596099 : Nat := 272075826368505327663197

theorem tailTrace_596099 : CollatzResearch.WordTrace tailWord_596099 prefixEnd_596099 272075826368505327663197 := by
  unfold tailWord_596099
  simp only [CollatzResearch.WordTrace]
  refine ⟨21741516667442603449151351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14494344444961735632767567 21741516667442603449151351)
  ·
    refine ⟨32612275001163905173727027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21741516667442603449151351 32612275001163905173727027)
    ·
      refine ⟨48918412501745857760590541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32612275001163905173727027 48918412501745857760590541)
      ·
        refine ⟨18344404688154696660221453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48918412501745857760590541 18344404688154696660221453)
        ·
          refine ⟨6879151758058011247583045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18344404688154696660221453 6879151758058011247583045)
          ·
            refine ⟨1289840954635877108921821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6879151758058011247583045 1289840954635877108921821)
            ·
              refine ⟨483690357988453915845683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1289840954635877108921821 483690357988453915845683)
              ·
                refine ⟨725535536982680873768525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 483690357988453915845683 725535536982680873768525)
                ·
                  refine ⟨272075826368505327663197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 725535536982680873768525 272075826368505327663197)
                  ·
                    rfl

theorem cell20_596099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 3, 1, 3].length) (baseStart_596099 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_596099 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_596099 prefixEnd_596099 := by exact prefixLift 596099
  have htrace : WordTrace (prefixWord ++ tailWord_596099) baseStart_596099 baseEnd_596099 := by
    simpa [prefixWord, tailWord_596099, baseEnd_596099] using wordTrace_append hprefix tailTrace_596099
  have hstable : (prefixWord ++ tailWord_596099).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596099).length < 2 ^ (prefixWord ++ tailWord_596099).sum := by decide
  have hdescent : baseEnd_596099 < baseStart_596099 := by decide
  rcases family_descends (prefixWord ++ tailWord_596099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596195 : List Nat := [1, 1, 1, 8, 1, 2, 2, 2, 2]
def baseStart_596195 : Nat := 118140960795 + 596195 * 2 ^ 59
def prefixEnd_596195 : Nat := 4983230072969 + 3 ^ 40 * 596195 * 2
def baseEnd_596195 : Nat := 272119643384355660462805

theorem tailTrace_596195 : CollatzResearch.WordTrace tailWord_596195 prefixEnd_596195 272119643384355660462805 := by
  unfold tailWord_596195
  simp only [CollatzResearch.WordTrace]
  refine ⟨21745018075094811844646039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14496678716729874563097359 21745018075094811844646039)
  ·
    refine ⟨32617527112642217766969059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21745018075094811844646039 32617527112642217766969059)
    ·
      refine ⟨48926290668963326650453589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32617527112642217766969059 48926290668963326650453589)
      ·
        refine ⟨573354968776913984185003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 48926290668963326650453589 573354968776913984185003)
        ·
          refine ⟨860032453165370976277505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 573354968776913984185003 860032453165370976277505)
          ·
            refine ⟨645024339874028232208129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 860032453165370976277505 645024339874028232208129)
            ·
              refine ⟨483768254905521174156097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 645024339874028232208129 483768254905521174156097)
              ·
                refine ⟨362826191179140880617073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 483768254905521174156097 362826191179140880617073)
                ·
                  refine ⟨272119643384355660462805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 362826191179140880617073 272119643384355660462805)
                  ·
                    rfl

theorem cell20_596195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 2, 2, 2].length) (baseStart_596195 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_596195 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_596195 prefixEnd_596195 := by exact prefixLift 596195
  have htrace : WordTrace (prefixWord ++ tailWord_596195) baseStart_596195 baseEnd_596195 := by
    simpa [prefixWord, tailWord_596195, baseEnd_596195] using wordTrace_append hprefix tailTrace_596195
  have hstable : (prefixWord ++ tailWord_596195).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596195).length < 2 ^ (prefixWord ++ tailWord_596195).sum := by decide
  have hdescent : baseEnd_596195 < baseStart_596195 := by decide
  rcases family_descends (prefixWord ++ tailWord_596195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596199 : List Nat := [1, 1, 5, 3, 1, 2, 1, 4, 2]
def baseStart_596199 : Nat := 118140960795 + 596199 * 2 ^ 59
def prefixEnd_596199 : Nat := 4983230072969 + 3 ^ 40 * 596199 * 2
def baseEnd_596199 : Nat := 272121469093349424329455

theorem tailTrace_596199 : CollatzResearch.WordTrace tailWord_596199 prefixEnd_596199 272121469093349424329455 := by
  unfold tailWord_596199
  simp only [CollatzResearch.WordTrace]
  refine ⟨21745163967080320527791651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14496775978053547018527767 21745163967080320527791651)
  ·
    refine ⟨32617745950620480791687477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21745163967080320527791651 32617745950620480791687477)
    ·
      refine ⟨3057913682870670074220701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32617745950620480791687477 3057913682870670074220701)
      ·
        refine ⟨1146717631076501277832763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3057913682870670074220701 1146717631076501277832763)
        ·
          refine ⟨1720076446614751916749145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1146717631076501277832763 1720076446614751916749145)
          ·
            refine ⟨1290057334961063937561859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1720076446614751916749145 1290057334961063937561859)
            ·
              refine ⟨1935086002441595906342789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1290057334961063937561859 1935086002441595906342789)
              ·
                refine ⟨362828625457799232439273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1935086002441595906342789 362828625457799232439273)
                ·
                  refine ⟨272121469093349424329455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 362828625457799232439273 272121469093349424329455)
                  ·
                    rfl

theorem cell20_596199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 4, 2].length) (baseStart_596199 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_596199 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_596199 prefixEnd_596199 := by exact prefixLift 596199
  have htrace : WordTrace (prefixWord ++ tailWord_596199) baseStart_596199 baseEnd_596199 := by
    simpa [prefixWord, tailWord_596199, baseEnd_596199] using wordTrace_append hprefix tailTrace_596199
  have hstable : (prefixWord ++ tailWord_596199).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596199).length < 2 ^ (prefixWord ++ tailWord_596199).sum := by decide
  have hdescent : baseEnd_596199 < baseStart_596199 := by decide
  rcases family_descends (prefixWord ++ tailWord_596199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596224 : List Nat := [2, 1, 1, 2, 1, 1, 5, 1, 6]
def baseStart_596224 : Nat := 118140960795 + 596224 * 2 ^ 59
def prefixEnd_596224 : Nat := 4983230072969 + 3 ^ 40 * 596224 * 2
def baseEnd_596224 : Nat := 272132879774560448496019

theorem tailTrace_596224 : CollatzResearch.WordTrace tailWord_596224 prefixEnd_596224 272132879774560448496019 := by
  unfold tailWord_596224
  simp only [CollatzResearch.WordTrace]
  refine ⟨10873037895994874898725863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14497383861326499864967817 10873037895994874898725863)
  ·
    refine ⟨16309556843992312348088795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10873037895994874898725863 16309556843992312348088795)
    ·
      refine ⟨24464335265988468522133193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16309556843992312348088795 24464335265988468522133193)
      ·
        refine ⟨18348251449491351391599895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24464335265988468522133193 18348251449491351391599895)
        ·
          refine ⟨27522377174237027087399843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18348251449491351391599895 27522377174237027087399843)
          ·
            refine ⟨41283565761355540631099765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27522377174237027087399843 41283565761355540631099765)
            ·
              refine ⟨3870334290127081934165603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41283565761355540631099765 3870334290127081934165603)
              ·
                refine ⟨5805501435190622901248405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3870334290127081934165603 5805501435190622901248405)
                ·
                  refine ⟨272132879774560448496019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5805501435190622901248405 272132879774560448496019)
                  ·
                    rfl

theorem cell20_596224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 6].length) (baseStart_596224 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_596224 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_596224 prefixEnd_596224 := by exact prefixLift 596224
  have htrace : WordTrace (prefixWord ++ tailWord_596224) baseStart_596224 baseEnd_596224 := by
    simpa [prefixWord, tailWord_596224, baseEnd_596224] using wordTrace_append hprefix tailTrace_596224
  have hstable : (prefixWord ++ tailWord_596224).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596224).length < 2 ^ (prefixWord ++ tailWord_596224).sum := by decide
  have hdescent : baseEnd_596224 < baseStart_596224 := by decide
  rcases family_descends (prefixWord ++ tailWord_596224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596254 : List Nat := [4, 3, 2, 1, 1, 1, 2, 4, 2]
def baseStart_596254 : Nat := 118140960795 + 596254 * 2 ^ 59
def prefixEnd_596254 : Nat := 4983230072969 + 3 ^ 40 * 596254 * 2
def baseEnd_596254 : Nat := 272146572592013677495897

theorem tailTrace_596254 : CollatzResearch.WordTrace tailWord_596254 prefixEnd_596254 272146572592013677495897 := by
  unfold tailWord_596254
  simp only [CollatzResearch.WordTrace]
  refine ⟨2718396247735133115130477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14498113321254043280695877 2718396247735133115130477)
  ·
    refine ⟨1019398592900674918173929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2718396247735133115130477 1019398592900674918173929)
    ·
      refine ⟨764548944675506188630447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1019398592900674918173929 764548944675506188630447)
      ·
        refine ⟨1146823417013259282945671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 764548944675506188630447 1146823417013259282945671)
        ·
          refine ⟨1720235125519888924418507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1146823417013259282945671 1720235125519888924418507)
          ·
            refine ⟨2580352688279833386627761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1720235125519888924418507 2580352688279833386627761)
            ·
              refine ⟨1935264516209875039970821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2580352688279833386627761 1935264516209875039970821)
              ·
                refine ⟨362862096789351569994529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1935264516209875039970821 362862096789351569994529)
                ·
                  refine ⟨272146572592013677495897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 362862096789351569994529 272146572592013677495897)
                  ·
                    rfl

theorem cell20_596254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_596254 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_596254 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_596254 prefixEnd_596254 := by exact prefixLift 596254
  have htrace : WordTrace (prefixWord ++ tailWord_596254) baseStart_596254 baseEnd_596254 := by
    simpa [prefixWord, tailWord_596254, baseEnd_596254] using wordTrace_append hprefix tailTrace_596254
  have hstable : (prefixWord ++ tailWord_596254).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596254).length < 2 ^ (prefixWord ++ tailWord_596254).sum := by decide
  have hdescent : baseEnd_596254 < baseStart_596254 := by decide
  rcases family_descends (prefixWord ++ tailWord_596254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596258 : List Nat := [3, 3, 1, 1, 3, 2, 2, 1, 4]
def baseStart_596258 : Nat := 118140960795 + 596258 * 2 ^ 59
def prefixEnd_596258 : Nat := 4983230072969 + 3 ^ 40 * 596258 * 2
def baseEnd_596258 : Nat := 272148398301007441362547

theorem tailTrace_596258 : CollatzResearch.WordTrace tailWord_596258 prefixEnd_596258 272148398301007441362547 := by
  unfold tailWord_596258
  simp only [CollatzResearch.WordTrace]
  refine ⟨5436828968466643401047357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14498210582577715736126285 5436828968466643401047357)
  ·
    refine ⟨2038810863174991275392759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5436828968466643401047357 2038810863174991275392759)
    ·
      refine ⟨3058216294762486913089139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2038810863174991275392759 3058216294762486913089139)
      ·
        refine ⟨4587324442143730369633709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3058216294762486913089139 4587324442143730369633709)
        ·
          refine ⟨1720246665803898888612641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4587324442143730369633709 1720246665803898888612641)
          ·
            refine ⟨1290184999352924166459481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1720246665803898888612641 1290184999352924166459481)
            ·
              refine ⟨967638749514693124844611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1290184999352924166459481 967638749514693124844611)
              ·
                refine ⟨1451458124272039687266917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 967638749514693124844611 1451458124272039687266917)
                ·
                  refine ⟨272148398301007441362547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1451458124272039687266917 272148398301007441362547)
                  ·
                    rfl

theorem cell20_596258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_596258 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_596258 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_596258 prefixEnd_596258 := by exact prefixLift 596258
  have htrace : WordTrace (prefixWord ++ tailWord_596258) baseStart_596258 baseEnd_596258 := by
    simpa [prefixWord, tailWord_596258, baseEnd_596258] using wordTrace_append hprefix tailTrace_596258
  have hstable : (prefixWord ++ tailWord_596258).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596258).length < 2 ^ (prefixWord ++ tailWord_596258).sum := by decide
  have hdescent : baseEnd_596258 < baseStart_596258 := by decide
  rcases family_descends (prefixWord ++ tailWord_596258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596296 : List Nat := [2, 1, 3, 1, 1, 2, 5, 3, 2]
def baseStart_596296 : Nat := 118140960795 + 596296 * 2 ^ 59
def prefixEnd_596296 : Nat := 4983230072969 + 3 ^ 40 * 596296 * 2
def baseEnd_596296 : Nat := 272165742536448198095725

theorem tailTrace_596296 : CollatzResearch.WordTrace tailWord_596296 prefixEnd_596296 272165742536448198095725 := by
  unfold tailWord_596296
  simp only [CollatzResearch.WordTrace]
  refine ⟨10874350923864453047036371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14499134565152604062715161 10874350923864453047036371)
  ·
    refine ⟨16311526385796679570554557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10874350923864453047036371 16311526385796679570554557)
    ·
      refine ⟨6116822394673754838957959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16311526385796679570554557 6116822394673754838957959)
      ·
        refine ⟨9175233592010632258436939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6116822394673754838957959 9175233592010632258436939)
        ·
          refine ⟨13762850388015948387655409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9175233592010632258436939 13762850388015948387655409)
          ·
            refine ⟨10322137791011961290741557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13762850388015948387655409 10322137791011961290741557)
            ·
              refine ⟨967700417907371371007021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10322137791011961290741557 967700417907371371007021)
              ·
                refine ⟨362887656715264264127633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 967700417907371371007021 362887656715264264127633)
                ·
                  refine ⟨272165742536448198095725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 362887656715264264127633 272165742536448198095725)
                  ·
                    rfl

theorem cell20_596296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 3, 2].length) (baseStart_596296 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_596296 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_596296 prefixEnd_596296 := by exact prefixLift 596296
  have htrace : WordTrace (prefixWord ++ tailWord_596296) baseStart_596296 baseEnd_596296 := by
    simpa [prefixWord, tailWord_596296, baseEnd_596296] using wordTrace_append hprefix tailTrace_596296
  have hstable : (prefixWord ++ tailWord_596296).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596296).length < 2 ^ (prefixWord ++ tailWord_596296).sum := by decide
  have hdescent : baseEnd_596296 < baseStart_596296 := by decide
  rcases family_descends (prefixWord ++ tailWord_596296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596324 : List Nat := [2, 3, 1, 1, 3, 1, 4, 5]
def baseStart_596324 : Nat := 118140960795 + 596324 * 2 ^ 59
def prefixEnd_596324 : Nat := 4983230072969 + 3 ^ 40 * 596324 * 2
def baseEnd_596324 : Nat := 90726174166468181720759

theorem tailTrace_596324 : CollatzResearch.WordTrace tailWord_596324 prefixEnd_596324 90726174166468181720759 := by
  unfold tailWord_596324
  simp only [CollatzResearch.WordTrace]
  refine ⟨10874861545813733438046013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14499815394418311250728017 10874861545813733438046013)
  ·
    refine ⟨4078073079680150039267255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10874861545813733438046013 4078073079680150039267255)
    ·
      refine ⟨6117109619520225058900883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4078073079680150039267255 6117109619520225058900883)
      ·
        refine ⟨9175664429280337588351325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6117109619520225058900883 9175664429280337588351325)
        ·
          refine ⟨3440874160980126595631747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9175664429280337588351325 3440874160980126595631747)
          ·
            refine ⟨5161311241470189893447621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3440874160980126595631747 5161311241470189893447621)
            ·
              refine ⟨967745857775660605021429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5161311241470189893447621 967745857775660605021429)
              ·
                refine ⟨90726174166468181720759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 967745857775660605021429 90726174166468181720759)
                ·
                  rfl

theorem cell20_596324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 5].length) (baseStart_596324 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_596324 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_596324 prefixEnd_596324 := by exact prefixLift 596324
  have htrace : WordTrace (prefixWord ++ tailWord_596324) baseStart_596324 baseEnd_596324 := by
    simpa [prefixWord, tailWord_596324, baseEnd_596324] using wordTrace_append hprefix tailTrace_596324
  have hstable : (prefixWord ++ tailWord_596324).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596324).length < 2 ^ (prefixWord ++ tailWord_596324).sum := by decide
  have hdescent : baseEnd_596324 < baseStart_596324 := by decide
  rcases family_descends (prefixWord ++ tailWord_596324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596327 : List Nat := [1, 1, 5, 1, 3, 1, 4, 1, 3]
def baseStart_596327 : Nat := 118140960795 + 596327 * 2 ^ 59
def prefixEnd_596327 : Nat := 4983230072969 + 3 ^ 40 * 596327 * 2
def baseEnd_596327 : Nat := 272179891781149868062265

theorem tailTrace_596327 : CollatzResearch.WordTrace tailWord_596327 prefixEnd_596327 272179891781149868062265 := by
  unfold tailWord_596327
  simp only [CollatzResearch.WordTrace]
  refine ⟨21749832510616598388451235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14499888340411065592300823 21749832510616598388451235)
  ·
    refine ⟨32624748765924897582676853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21749832510616598388451235 32624748765924897582676853)
    ·
      refine ⟨3058570196805459148375955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32624748765924897582676853 3058570196805459148375955)
      ·
        refine ⟨4587855295208188722563933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3058570196805459148375955 4587855295208188722563933)
        ·
          refine ⟨1720445735703070770961475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4587855295208188722563933 1720445735703070770961475)
          ·
            refine ⟨2580668603554606156442213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1720445735703070770961475 2580668603554606156442213)
            ·
              refine ⟨483875363166488654332915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2580668603554606156442213 483875363166488654332915)
              ·
                refine ⟨725813044749732981499373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 483875363166488654332915 725813044749732981499373)
                ·
                  refine ⟨272179891781149868062265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 725813044749732981499373 272179891781149868062265)
                  ·
                    rfl

theorem cell20_596327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 4, 1, 3].length) (baseStart_596327 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_596327 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_596327 prefixEnd_596327 := by exact prefixLift 596327
  have htrace : WordTrace (prefixWord ++ tailWord_596327) baseStart_596327 baseEnd_596327 := by
    simpa [prefixWord, tailWord_596327, baseEnd_596327] using wordTrace_append hprefix tailTrace_596327
  have hstable : (prefixWord ++ tailWord_596327).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596327).length < 2 ^ (prefixWord ++ tailWord_596327).sum := by decide
  have hdescent : baseEnd_596327 < baseStart_596327 := by decide
  rcases family_descends (prefixWord ++ tailWord_596327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596331 : List Nat := [1, 1, 1, 1, 2, 2, 2, 7, 3]
def baseStart_596331 : Nat := 118140960795 + 596331 * 2 ^ 59
def prefixEnd_596331 : Nat := 4983230072969 + 3 ^ 40 * 596331 * 2
def baseEnd_596331 : Nat := 272181717490143631928915

theorem tailTrace_596331 : CollatzResearch.WordTrace tailWord_596331 prefixEnd_596331 272181717490143631928915 := by
  unfold tailWord_596331
  simp only [CollatzResearch.WordTrace]
  refine ⟨21749978402602107071596847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14499985601734738047731231 21749978402602107071596847)
  ·
    refine ⟨32624967603903160607395271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21749978402602107071596847 32624967603903160607395271)
    ·
      refine ⟨48937451405854740911092907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32624967603903160607395271 48937451405854740911092907)
      ·
        refine ⟨73406177108782111366639361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48937451405854740911092907 73406177108782111366639361)
        ·
          refine ⟨55054632831586583524979521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73406177108782111366639361 55054632831586583524979521)
          ·
            refine ⟨41290974623689937643734641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55054632831586583524979521 41290974623689937643734641)
            ·
              refine ⟨30968230967767453232800981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41290974623689937643734641 30968230967767453232800981)
              ·
                refine ⟨725817913307049685143773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 30968230967767453232800981 725817913307049685143773)
                ·
                  refine ⟨272181717490143631928915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 725817913307049685143773 272181717490143631928915)
                  ·
                    rfl

theorem cell20_596331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 7, 3].length) (baseStart_596331 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_596331 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_596331 prefixEnd_596331 := by exact prefixLift 596331
  have htrace : WordTrace (prefixWord ++ tailWord_596331) baseStart_596331 baseEnd_596331 := by
    simpa [prefixWord, tailWord_596331, baseEnd_596331] using wordTrace_append hprefix tailTrace_596331
  have hstable : (prefixWord ++ tailWord_596331).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596331).length < 2 ^ (prefixWord ++ tailWord_596331).sum := by decide
  have hdescent : baseEnd_596331 < baseStart_596331 := by decide
  rcases family_descends (prefixWord ++ tailWord_596331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596362 : List Nat := [3, 1, 2, 5, 9]
def baseStart_596362 : Nat := 118140960795 + 596362 * 2 ^ 59
def prefixEnd_596362 : Nat := 4983230072969 + 3 ^ 40 * 596362 * 2
def baseEnd_596362 : Nat := 3360442799195621011055

theorem tailTrace_596362 : CollatzResearch.WordTrace tailWord_596362 prefixEnd_596362 3360442799195621011055 := by
  unfold tailWord_596362
  simp only [CollatzResearch.WordTrace]
  refine ⟨5437777266372449841493835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14500739376993199577316893 5437777266372449841493835)
  ·
    refine ⟨8156665899558674762240753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5437777266372449841493835 8156665899558674762240753)
    ·
      refine ⟨6117499424669006071680565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8156665899558674762240753 6117499424669006071680565)
      ·
        refine ⟨573515571062719319220053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6117499424669006071680565 573515571062719319220053)
        ·
          refine ⟨3360442799195621011055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 573515571062719319220053 3360442799195621011055)
          ·
            rfl

theorem cell20_596362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 9].length) (baseStart_596362 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_596362 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_596362 prefixEnd_596362 := by exact prefixLift 596362
  have htrace : WordTrace (prefixWord ++ tailWord_596362) baseStart_596362 baseEnd_596362 := by
    simpa [prefixWord, tailWord_596362, baseEnd_596362] using wordTrace_append hprefix tailTrace_596362
  have hstable : (prefixWord ++ tailWord_596362).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596362).length < 2 ^ (prefixWord ++ tailWord_596362).sum := by decide
  have hdescent : baseEnd_596362 < baseStart_596362 := by decide
  rcases family_descends (prefixWord ++ tailWord_596362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596386 : List Nat := [3, 3, 1, 2, 1, 1, 1, 5, 3]
def baseStart_596386 : Nat := 118140960795 + 596386 * 2 ^ 59
def prefixEnd_596386 : Nat := 4983230072969 + 3 ^ 40 * 596386 * 2
def baseEnd_596386 : Nat := 272206820988807885095357

theorem tailTrace_596386 : CollatzResearch.WordTrace tailWord_596386 prefixEnd_596386 272206820988807885095357 := by
  unfold tailWord_596386
  simp only [CollatzResearch.WordTrace]
  refine ⟨5437996104350712866212253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14501322944935234309899341 5437996104350712866212253)
  ·
    refine ⟨2039248539131517324829595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5437996104350712866212253 2039248539131517324829595)
    ·
      refine ⟨3058872808697275987244393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2039248539131517324829595 3058872808697275987244393)
      ·
        refine ⟨2294154606522956990433295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3058872808697275987244393 2294154606522956990433295)
        ·
          refine ⟨3441231909784435485649943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2294154606522956990433295 3441231909784435485649943)
          ·
            refine ⟨5161847864676653228474915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3441231909784435485649943 5161847864676653228474915)
            ·
              refine ⟨7742771797014979842712373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5161847864676653228474915 7742771797014979842712373)
              ·
                refine ⟨725884855970154360254285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7742771797014979842712373 725884855970154360254285)
                ·
                  refine ⟨272206820988807885095357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 725884855970154360254285 272206820988807885095357)
                  ·
                    rfl

theorem cell20_596386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_596386 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_596386 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_596386 prefixEnd_596386 := by exact prefixLift 596386
  have htrace : WordTrace (prefixWord ++ tailWord_596386) baseStart_596386 baseEnd_596386 := by
    simpa [prefixWord, tailWord_596386, baseEnd_596386] using wordTrace_append hprefix tailTrace_596386
  have hstable : (prefixWord ++ tailWord_596386).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596386).length < 2 ^ (prefixWord ++ tailWord_596386).sum := by decide
  have hdescent : baseEnd_596386 < baseStart_596386 := by decide
  rcases family_descends (prefixWord ++ tailWord_596386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596420 : List Nat := [2, 3, 3, 2, 2, 2, 1, 2, 3]
def baseStart_596420 : Nat := 118140960795 + 596420 * 2 ^ 59
def prefixEnd_596420 : Nat := 4983230072969 + 3 ^ 40 * 596420 * 2
def baseEnd_596420 : Nat := 272222339515254877961885

theorem tailTrace_596420 : CollatzResearch.WordTrace tailWord_596420 prefixEnd_596420 272222339515254877961885 := by
  unfold tailWord_596420
  simp only [CollatzResearch.WordTrace]
  refine ⟨10876612249639837635793357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14502149666186450181057809 10876612249639837635793357)
  ·
    refine ⟨4078729593614939113422509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10876612249639837635793357 4078729593614939113422509)
    ·
      refine ⟨1529523597605602167533441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4078729593614939113422509 1529523597605602167533441)
      ·
        refine ⟨1147142698204201625650081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1529523597605602167533441 1147142698204201625650081)
        ·
          refine ⟨860357023653151219237561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1147142698204201625650081 860357023653151219237561)
          ·
            refine ⟨645267767739863414428171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 860357023653151219237561 645267767739863414428171)
            ·
              refine ⟨967901651609795121642257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 645267767739863414428171 967901651609795121642257)
              ·
                refine ⟨725926238707346341231693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 967901651609795121642257 725926238707346341231693)
                ·
                  refine ⟨272222339515254877961885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 725926238707346341231693 272222339515254877961885)
                  ·
                    rfl

theorem cell20_596420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 2, 3].length) (baseStart_596420 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_596420 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_596420 prefixEnd_596420 := by exact prefixLift 596420
  have htrace : WordTrace (prefixWord ++ tailWord_596420) baseStart_596420 baseEnd_596420 := by
    simpa [prefixWord, tailWord_596420, baseEnd_596420] using wordTrace_append hprefix tailTrace_596420
  have hstable : (prefixWord ++ tailWord_596420).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596420).length < 2 ^ (prefixWord ++ tailWord_596420).sum := by decide
  have hdescent : baseEnd_596420 < baseStart_596420 := by decide
  rcases family_descends (prefixWord ++ tailWord_596420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596424 : List Nat := [2, 1, 3, 1, 3, 2, 3, 2, 3]
def baseStart_596424 : Nat := 118140960795 + 596424 * 2 ^ 59
def prefixEnd_596424 : Nat := 4983230072969 + 3 ^ 40 * 596424 * 2
def baseEnd_596424 : Nat := 272224165224248641828535

theorem tailTrace_596424 : CollatzResearch.WordTrace tailWord_596424 prefixEnd_596424 272224165224248641828535 := by
  unfold tailWord_596424
  simp only [CollatzResearch.WordTrace]
  refine ⟨10876685195632591977366163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14502246927510122636488217 10876685195632591977366163)
  ·
    refine ⟨16315027793448887966049245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10876685195632591977366163 16315027793448887966049245)
    ·
      refine ⟨6118135422543332987268467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16315027793448887966049245 6118135422543332987268467)
      ·
        refine ⟨9177203133814999480902701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6118135422543332987268467 9177203133814999480902701)
        ·
          refine ⟨3441451175180624805338513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9177203133814999480902701 3441451175180624805338513)
          ·
            refine ⟨2581088381385468604003885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3441451175180624805338513 2581088381385468604003885)
            ·
              refine ⟨967908143019550726501457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2581088381385468604003885 967908143019550726501457)
              ·
                refine ⟨725931107264663044876093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 967908143019550726501457 725931107264663044876093)
                ·
                  refine ⟨272224165224248641828535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 725931107264663044876093 272224165224248641828535)
                  ·
                    rfl

theorem cell20_596424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 2, 3].length) (baseStart_596424 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_596424 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_596424 prefixEnd_596424 := by exact prefixLift 596424
  have htrace : WordTrace (prefixWord ++ tailWord_596424) baseStart_596424 baseEnd_596424 := by
    simpa [prefixWord, tailWord_596424, baseEnd_596424] using wordTrace_append hprefix tailTrace_596424
  have hstable : (prefixWord ++ tailWord_596424).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596424).length < 2 ^ (prefixWord ++ tailWord_596424).sum := by decide
  have hdescent : baseEnd_596424 < baseStart_596424 := by decide
  rcases family_descends (prefixWord ++ tailWord_596424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596459 : List Nat := [1, 1, 1, 1, 2, 3, 5, 6]
def baseStart_596459 : Nat := 118140960795 + 596459 * 2 ^ 59
def prefixEnd_596459 : Nat := 4983230072969 + 3 ^ 40 * 596459 * 2
def baseEnd_596459 : Nat := 90746713392648025220575

theorem tailTrace_596459 : CollatzResearch.WordTrace tailWord_596459 prefixEnd_596459 90746713392648025220575 := by
  unfold tailWord_596459
  simp only [CollatzResearch.WordTrace]
  refine ⟨21754646946138384932256431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14503097964092256621504287 21754646946138384932256431)
  ·
    refine ⟨32631970419207577398384647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21754646946138384932256431 32631970419207577398384647)
    ·
      refine ⟨48947955628811366097576971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32631970419207577398384647 48947955628811366097576971)
      ·
        refine ⟨73421933443217049146365457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48947955628811366097576971 73421933443217049146365457)
        ·
          refine ⟨55066450082412786859774093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73421933443217049146365457 55066450082412786859774093)
          ·
            refine ⟨20649918780904795072415285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55066450082412786859774093 20649918780904795072415285)
            ·
              refine ⟨1935929885709824538038933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20649918780904795072415285 1935929885709824538038933)
              ·
                refine ⟨90746713392648025220575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1935929885709824538038933 90746713392648025220575)
                ·
                  rfl

theorem cell20_596459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 6].length) (baseStart_596459 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_596459 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_596459 prefixEnd_596459 := by exact prefixLift 596459
  have htrace : WordTrace (prefixWord ++ tailWord_596459) baseStart_596459 baseEnd_596459 := by
    simpa [prefixWord, tailWord_596459, baseEnd_596459] using wordTrace_append hprefix tailTrace_596459
  have hstable : (prefixWord ++ tailWord_596459).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596459).length < 2 ^ (prefixWord ++ tailWord_596459).sum := by decide
  have hdescent : baseEnd_596459 < baseStart_596459 := by decide
  rcases family_descends (prefixWord ++ tailWord_596459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596482 : List Nat := [3, 4, 1, 2, 3, 1, 1, 1, 4]
def baseStart_596482 : Nat := 118140960795 + 596482 * 2 ^ 59
def prefixEnd_596482 : Nat := 4983230072969 + 3 ^ 40 * 596482 * 2
def baseEnd_596482 : Nat := 272250638004658217894965

theorem tailTrace_596482 : CollatzResearch.WordTrace tailWord_596482 prefixEnd_596482 272250638004658217894965 := by
  unfold tailWord_596482
  simp only [CollatzResearch.WordTrace]
  refine ⟨5438871456263764965085925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14503657216703373240229133 5438871456263764965085925)
  ·
    refine ⟨1019788398049455930953611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5438871456263764965085925 1019788398049455930953611)
    ·
      refine ⟨1529682597074183896430417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1019788398049455930953611 1529682597074183896430417)
      ·
        refine ⟨1147261947805637922322813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1529682597074183896430417 1147261947805637922322813)
        ·
          refine ⟨430223230427114220871055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1147261947805637922322813 430223230427114220871055)
          ·
            refine ⟨645334845640671331306583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 430223230427114220871055 645334845640671331306583)
            ·
              refine ⟨968002268461006996959875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 645334845640671331306583 968002268461006996959875)
              ·
                refine ⟨1452003402691510495439813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 968002268461006996959875 1452003402691510495439813)
                ·
                  refine ⟨272250638004658217894965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1452003402691510495439813 272250638004658217894965)
                  ·
                    rfl

theorem cell20_596482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_596482 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_596482 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_596482 prefixEnd_596482 := by exact prefixLift 596482
  have htrace : WordTrace (prefixWord ++ tailWord_596482) baseStart_596482 baseEnd_596482 := by
    simpa [prefixWord, tailWord_596482, baseEnd_596482] using wordTrace_append hprefix tailTrace_596482
  have hstable : (prefixWord ++ tailWord_596482).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596482).length < 2 ^ (prefixWord ++ tailWord_596482).sum := by decide
  have hdescent : baseEnd_596482 < baseStart_596482 := by decide
  rcases family_descends (prefixWord ++ tailWord_596482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596483 : List Nat := [1, 1, 1, 3, 2, 1, 4, 4, 3]
def baseStart_596483 : Nat := 118140960795 + 596483 * 2 ^ 59
def prefixEnd_596483 : Nat := 4983230072969 + 3 ^ 40 * 596483 * 2
def baseEnd_596483 : Nat := 272251094431906658861627

theorem tailTrace_596483 : CollatzResearch.WordTrace tailWord_596483 prefixEnd_596483 272251094431906658861627 := by
  unfold tailWord_596483
  simp only [CollatzResearch.WordTrace]
  refine ⟨21755522298051437031130103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14503681532034291354086735 21755522298051437031130103)
  ·
    refine ⟨32633283447077155546695155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21755522298051437031130103 32633283447077155546695155)
    ·
      refine ⟨48949925170615733320042733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32633283447077155546695155 48949925170615733320042733)
      ·
        refine ⟨18356221938980899995016025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48949925170615733320042733 18356221938980899995016025)
        ·
          refine ⟨13767166454235674996262019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18356221938980899995016025 13767166454235674996262019)
          ·
            refine ⟨20650749681353512494393029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13767166454235674996262019 20650749681353512494393029)
            ·
              refine ⟨3872015565253783592698693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20650749681353512494393029 3872015565253783592698693)
              ·
                refine ⟨726002918485084423631005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3872015565253783592698693 726002918485084423631005)
                ·
                  refine ⟨272251094431906658861627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 726002918485084423631005 272251094431906658861627)
                  ·
                    rfl

theorem cell20_596483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 4, 3].length) (baseStart_596483 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_596483 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_596483 prefixEnd_596483 := by exact prefixLift 596483
  have htrace : WordTrace (prefixWord ++ tailWord_596483) baseStart_596483 baseEnd_596483 := by
    simpa [prefixWord, tailWord_596483, baseEnd_596483] using wordTrace_append hprefix tailTrace_596483
  have hstable : (prefixWord ++ tailWord_596483).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596483).length < 2 ^ (prefixWord ++ tailWord_596483).sum := by decide
  have hdescent : baseEnd_596483 < baseStart_596483 := by decide
  rcases family_descends (prefixWord ++ tailWord_596483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596538 : List Nat := [3, 1, 1, 1, 3, 4, 2, 2, 3]
def baseStart_596538 : Nat := 118140960795 + 596538 * 2 ^ 59
def prefixEnd_596538 : Nat := 4983230072969 + 3 ^ 40 * 596538 * 2
def baseEnd_596538 : Nat := 272276197930570912028069

theorem tailTrace_596538 : CollatzResearch.WordTrace tailWord_596538 prefixEnd_596538 272276197930570912028069 := by
  unfold tailWord_596538
  simp only [CollatzResearch.WordTrace]
  refine ⟨5439382078213045356095567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14505018875234787616254845 5439382078213045356095567)
  ·
    refine ⟨8159073117319568034143351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5439382078213045356095567 8159073117319568034143351)
    ·
      refine ⟨12238609675979352051215027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8159073117319568034143351 12238609675979352051215027)
      ·
        refine ⟨18357914513969028076822541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12238609675979352051215027 18357914513969028076822541)
        ·
          refine ⟨6884217942738385528808453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18357914513969028076822541 6884217942738385528808453)
          ·
            refine ⟨1290790864263447286651585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6884217942738385528808453 1290790864263447286651585)
            ·
              refine ⟨968093148197585464988689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1290790864263447286651585 968093148197585464988689)
              ·
                refine ⟨726069861148189098741517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 968093148197585464988689 726069861148189098741517)
                ·
                  refine ⟨272276197930570912028069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 726069861148189098741517 272276197930570912028069)
                  ·
                    rfl

theorem cell20_596538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 2, 3].length) (baseStart_596538 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_596538 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_596538 prefixEnd_596538 := by exact prefixLift 596538
  have htrace : WordTrace (prefixWord ++ tailWord_596538) baseStart_596538 baseEnd_596538 := by
    simpa [prefixWord, tailWord_596538, baseEnd_596538] using wordTrace_append hprefix tailTrace_596538
  have hstable : (prefixWord ++ tailWord_596538).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596538).length < 2 ^ (prefixWord ++ tailWord_596538).sum := by decide
  have hdescent : baseEnd_596538 < baseStart_596538 := by decide
  rcases family_descends (prefixWord ++ tailWord_596538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596541 : List Nat := [1, 4, 1, 3, 2, 1, 4, 2, 2]
def baseStart_596541 : Nat := 118140960795 + 596541 * 2 ^ 59
def prefixEnd_596541 : Nat := 4983230072969 + 3 ^ 40 * 596541 * 2
def baseEnd_596541 : Nat := 272277567212316234928057

theorem tailTrace_596541 : CollatzResearch.WordTrace tailWord_596541 prefixEnd_596541 272277567212316234928057 := by
  unfold tailWord_596541
  simp only [CollatzResearch.WordTrace]
  refine ⟨21757637731841312936741477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14505091821227541957827651 21757637731841312936741477)
  ·
    refine ⟨4079557074720246175639027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21757637731841312936741477 4079557074720246175639027)
    ·
      refine ⟨6119335612080369263458541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4079557074720246175639027 6119335612080369263458541)
      ·
        refine ⟨2294750854530138473796953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6119335612080369263458541 2294750854530138473796953)
        ·
          refine ⟨1721063140897603855347715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2294750854530138473796953 1721063140897603855347715)
          ·
            refine ⟨2581594711346405783021573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1721063140897603855347715 2581594711346405783021573)
            ·
              refine ⟨484049008377451084316545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2581594711346405783021573 484049008377451084316545)
              ·
                refine ⟨363036756283088313237409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 484049008377451084316545 363036756283088313237409)
                ·
                  refine ⟨272277567212316234928057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 363036756283088313237409 272277567212316234928057)
                  ·
                    rfl

theorem cell20_596541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 4, 2, 2].length) (baseStart_596541 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_596541 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_596541 prefixEnd_596541 := by exact prefixLift 596541
  have htrace : WordTrace (prefixWord ++ tailWord_596541) baseStart_596541 baseEnd_596541 := by
    simpa [prefixWord, tailWord_596541, baseEnd_596541] using wordTrace_append hprefix tailTrace_596541
  have hstable : (prefixWord ++ tailWord_596541).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596541).length < 2 ^ (prefixWord ++ tailWord_596541).sum := by decide
  have hdescent : baseEnd_596541 < baseStart_596541 := by decide
  rcases family_descends (prefixWord ++ tailWord_596541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596559 : List Nat := [1, 1, 2, 1, 1, 2, 6, 3, 3]
def baseStart_596559 : Nat := 118140960795 + 596559 * 2 ^ 59
def prefixEnd_596559 : Nat := 4983230072969 + 3 ^ 40 * 596559 * 2
def baseEnd_596559 : Nat := 272285782902788172327983

theorem tailTrace_596559 : CollatzResearch.WordTrace tailWord_596559 prefixEnd_596559 272285782902788172327983 := by
  unfold tailWord_596559
  simp only [CollatzResearch.WordTrace]
  refine ⟨21758294245776102010896731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14505529497184068007264487 21758294245776102010896731)
  ·
    refine ⟨32637441368664153016345097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21758294245776102010896731 32637441368664153016345097)
    ·
      refine ⟨24478081026498114762258823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32637441368664153016345097 24478081026498114762258823)
      ·
        refine ⟨36717121539747172143388235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24478081026498114762258823 36717121539747172143388235)
        ·
          refine ⟨55075682309620758215082353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36717121539747172143388235 55075682309620758215082353)
          ·
            refine ⟨41306761732215568661311765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55075682309620758215082353 41306761732215568661311765)
            ·
              refine ⟨1936254456197604780998989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 41306761732215568661311765 1936254456197604780998989)
              ·
                refine ⟨726095421074101792874621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1936254456197604780998989 726095421074101792874621)
                ·
                  refine ⟨272285782902788172327983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 726095421074101792874621 272285782902788172327983)
                  ·
                    rfl

theorem cell20_596559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 3, 3].length) (baseStart_596559 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_596559 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_596559 prefixEnd_596559 := by exact prefixLift 596559
  have htrace : WordTrace (prefixWord ++ tailWord_596559) baseStart_596559 baseEnd_596559 := by
    simpa [prefixWord, tailWord_596559, baseEnd_596559] using wordTrace_append hprefix tailTrace_596559
  have hstable : (prefixWord ++ tailWord_596559).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596559).length < 2 ^ (prefixWord ++ tailWord_596559).sum := by decide
  have hdescent : baseEnd_596559 < baseStart_596559 := by decide
  rcases family_descends (prefixWord ++ tailWord_596559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596590 : List Nat := [4, 1, 2, 2, 2, 2, 7]
def baseStart_596590 : Nat := 118140960795 + 596590 * 2 ^ 59
def prefixEnd_596590 : Nat := 4983230072969 + 3 ^ 40 * 596590 * 2
def baseEnd_596590 : Nat := 30255548016387760254947

theorem tailTrace_596590 : CollatzResearch.WordTrace tailWord_596590 prefixEnd_596590 30255548016387760254947 := by
  unfold tailWord_596590
  simp only [CollatzResearch.WordTrace]
  refine ⟨2719928113582974288159403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14506283272442529536850149 2719928113582974288159403)
  ·
    refine ⟨4079892170374461432239105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2719928113582974288159403 4079892170374461432239105)
    ·
      refine ⟨3059919127780846074179329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4079892170374461432239105 3059919127780846074179329)
      ·
        refine ⟨2294939345835634555634497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3059919127780846074179329 2294939345835634555634497)
        ·
          refine ⟨1721204509376725916725873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2294939345835634555634497 1721204509376725916725873)
          ·
            refine ⟨1290903382032544437544405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1721204509376725916725873 1290903382032544437544405)
            ·
              refine ⟨30255548016387760254947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1290903382032544437544405 30255548016387760254947)
              ·
                rfl

theorem cell20_596590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 7].length) (baseStart_596590 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_596590 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_596590 prefixEnd_596590 := by exact prefixLift 596590
  have htrace : WordTrace (prefixWord ++ tailWord_596590) baseStart_596590 baseEnd_596590 := by
    simpa [prefixWord, tailWord_596590, baseEnd_596590] using wordTrace_append hprefix tailTrace_596590
  have hstable : (prefixWord ++ tailWord_596590).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596590).length < 2 ^ (prefixWord ++ tailWord_596590).sum := by decide
  have hdescent : baseEnd_596590 < baseStart_596590 := by decide
  rcases family_descends (prefixWord ++ tailWord_596590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596604 : List Nat := [2, 2, 2, 1, 1, 2, 3, 3, 4]
def baseStart_596604 : Nat := 118140960795 + 596604 * 2 ^ 59
def prefixEnd_596604 : Nat := 4983230072969 + 3 ^ 40 * 596604 * 2
def baseEnd_596604 : Nat := 272306322128968015827799

theorem tailTrace_596604 : CollatzResearch.WordTrace tailWord_596604 prefixEnd_596604 272306322128968015827799 := by
  unfold tailWord_596604
  simp only [CollatzResearch.WordTrace]
  refine ⟨10879967765306537348142433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14506623687075383130856577 10879967765306537348142433)
  ·
    refine ⟨8159975823979903011106825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10879967765306537348142433 8159975823979903011106825)
    ·
      refine ⟨6119981867984927258330119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8159975823979903011106825 6119981867984927258330119)
      ·
        refine ⟨9179972801977390887495179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6119981867984927258330119 9179972801977390887495179)
        ·
          refine ⟨13769959202966086331242769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9179972801977390887495179 13769959202966086331242769)
          ·
            refine ⟨10327469402224564748432077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13769959202966086331242769 10327469402224564748432077)
            ·
              refine ⟨3872801025834211780662029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10327469402224564748432077 3872801025834211780662029)
              ·
                refine ⟨1452300384687829417748261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3872801025834211780662029 1452300384687829417748261)
                ·
                  refine ⟨272306322128968015827799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1452300384687829417748261 272306322128968015827799)
                  ·
                    rfl

theorem cell20_596604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 3, 4].length) (baseStart_596604 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_596604 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_596604 prefixEnd_596604 := by exact prefixLift 596604
  have htrace : WordTrace (prefixWord ++ tailWord_596604) baseStart_596604 baseEnd_596604 := by
    simpa [prefixWord, tailWord_596604, baseEnd_596604] using wordTrace_append hprefix tailTrace_596604
  have hstable : (prefixWord ++ tailWord_596604).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596604).length < 2 ^ (prefixWord ++ tailWord_596604).sum := by decide
  have hdescent : baseEnd_596604 < baseStart_596604 := by decide
  rcases family_descends (prefixWord ++ tailWord_596604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596634 : List Nat := [3, 1, 1, 6, 1, 2, 1, 3, 2]
def baseStart_596634 : Nat := 118140960795 + 596634 * 2 ^ 59
def prefixEnd_596634 : Nat := 4983230072969 + 3 ^ 40 * 596634 * 2
def baseEnd_596634 : Nat := 272320014946421244827677

theorem tailTrace_596634 : CollatzResearch.WordTrace tailWord_596634 prefixEnd_596634 272320014946421244827677 := by
  unfold tailWord_596634
  simp only [CollatzResearch.WordTrace]
  refine ⟨5440257430126097454969239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14507353147002926546584637 5440257430126097454969239)
  ·
    refine ⟨8160386145189146182453859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5440257430126097454969239 8160386145189146182453859)
    ·
      refine ⟨12240579217783719273680789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8160386145189146182453859 12240579217783719273680789)
      ·
        refine ⟨573777150833611840953787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 12240579217783719273680789 573777150833611840953787)
        ·
          refine ⟨860665726250417761430681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 573777150833611840953787 860665726250417761430681)
          ·
            refine ⟨645499294687813321073011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 860665726250417761430681 645499294687813321073011)
            ·
              refine ⟨968248942031719981609517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 645499294687813321073011 968248942031719981609517)
              ·
                refine ⟨363093353261894993103569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 968248942031719981609517 363093353261894993103569)
                ·
                  refine ⟨272320014946421244827677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 363093353261894993103569 272320014946421244827677)
                  ·
                    rfl

theorem cell20_596634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 3, 2].length) (baseStart_596634 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_596634 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_596634 prefixEnd_596634 := by exact prefixLift 596634
  have htrace : WordTrace (prefixWord ++ tailWord_596634) baseStart_596634 baseEnd_596634 := by
    simpa [prefixWord, tailWord_596634, baseEnd_596634] using wordTrace_append hprefix tailTrace_596634
  have hstable : (prefixWord ++ tailWord_596634).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596634).length < 2 ^ (prefixWord ++ tailWord_596634).sum := by decide
  have hdescent : baseEnd_596634 < baseStart_596634 := by decide
  rcases family_descends (prefixWord ++ tailWord_596634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596659 : List Nat := [1, 1, 1, 2, 3, 6, 1, 1, 4]
def baseStart_596659 : Nat := 118140960795 + 596659 * 2 ^ 59
def prefixEnd_596659 : Nat := 4983230072969 + 3 ^ 40 * 596659 * 2
def baseEnd_596659 : Nat := 272331425627632268994241

theorem tailTrace_596659 : CollatzResearch.WordTrace tailWord_596659 prefixEnd_596659 272331425627632268994241 := by
  unfold tailWord_596659
  simp only [CollatzResearch.WordTrace]
  refine ⟨21761941545413819089537031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14507961030275879393024687 21761941545413819089537031)
  ·
    refine ⟨32642912318120728634305547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21761941545413819089537031 32642912318120728634305547)
    ·
      refine ⟨48964368477181092951458321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32642912318120728634305547 48964368477181092951458321)
      ·
        refine ⟨36723276357885819713593741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48964368477181092951458321 36723276357885819713593741)
        ·
          refine ⟨13771228634207182392597653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36723276357885819713593741 13771228634207182392597653)
          ·
            refine ⟨645526342228461674653015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 13771228634207182392597653 645526342228461674653015)
            ·
              refine ⟨968289513342692511979523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 645526342228461674653015 968289513342692511979523)
              ·
                refine ⟨1452434270014038767969285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 968289513342692511979523 1452434270014038767969285)
                ·
                  refine ⟨272331425627632268994241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1452434270014038767969285 272331425627632268994241)
                  ·
                    rfl

theorem cell20_596659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 1, 4].length) (baseStart_596659 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_596659 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_596659 prefixEnd_596659 := by exact prefixLift 596659
  have htrace : WordTrace (prefixWord ++ tailWord_596659) baseStart_596659 baseEnd_596659 := by
    simpa [prefixWord, tailWord_596659, baseEnd_596659] using wordTrace_append hprefix tailTrace_596659
  have hstable : (prefixWord ++ tailWord_596659).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596659).length < 2 ^ (prefixWord ++ tailWord_596659).sum := by decide
  have hdescent : baseEnd_596659 < baseStart_596659 := by decide
  rcases family_descends (prefixWord ++ tailWord_596659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596662 : List Nat := [5, 1, 3, 1, 2, 1, 2, 5]
def baseStart_596662 : Nat := 118140960795 + 596662 * 2 ^ 59
def prefixEnd_596662 : Nat := 4983230072969 + 3 ^ 40 * 596662 * 2
def baseEnd_596662 : Nat := 90777598303125863964743

theorem tailTrace_596662 : CollatzResearch.WordTrace tailWord_596662 prefixEnd_596662 90777598303125863964743 := by
  unfold tailWord_596662
  simp only [CollatzResearch.WordTrace]
  refine ⟨1360128185275184412618515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14508033976268633734597493 1360128185275184412618515)
  ·
    refine ⟨2040192277912776618927773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1360128185275184412618515 2040192277912776618927773)
    ·
      refine ⟨765072104217291232097915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2040192277912776618927773 765072104217291232097915)
      ·
        refine ⟨1147608156325936848146873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 765072104217291232097915 1147608156325936848146873)
        ·
          refine ⟨860706117244452636110155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1147608156325936848146873 860706117244452636110155)
          ·
            refine ⟨1291059175866678954165233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 860706117244452636110155 1291059175866678954165233)
            ·
              refine ⟨968294381900009215623925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1291059175866678954165233 968294381900009215623925)
              ·
                refine ⟨90777598303125863964743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 968294381900009215623925 90777598303125863964743)
                ·
                  rfl

theorem cell20_596662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_596662 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_596662 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_596662 prefixEnd_596662 := by exact prefixLift 596662
  have htrace : WordTrace (prefixWord ++ tailWord_596662) baseStart_596662 baseEnd_596662 := by
    simpa [prefixWord, tailWord_596662, baseEnd_596662] using wordTrace_append hprefix tailTrace_596662
  have hstable : (prefixWord ++ tailWord_596662).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596662).length < 2 ^ (prefixWord ++ tailWord_596662).sum := by decide
  have hdescent : baseEnd_596662 < baseStart_596662 := by decide
  rcases family_descends (prefixWord ++ tailWord_596662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596669 : List Nat := [1, 4, 1, 2, 1, 5, 2, 1, 3]
def baseStart_596669 : Nat := 118140960795 + 596669 * 2 ^ 59
def prefixEnd_596669 : Nat := 4983230072969 + 3 ^ 40 * 596669 * 2
def baseEnd_596669 : Nat := 272335989900116678660867

theorem tailTrace_596669 : CollatzResearch.WordTrace tailWord_596669 prefixEnd_596669 272335989900116678660867 := by
  unfold tailWord_596669
  simp only [CollatzResearch.WordTrace]
  refine ⟨21762306275377590797401061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14508204183585060531600707 21762306275377590797401061)
  ·
    refine ⟨4080432426633298274512699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21762306275377590797401061 4080432426633298274512699)
    ·
      refine ⟨6120648639949947411769049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4080432426633298274512699 6120648639949947411769049)
      ·
        refine ⟨4590486479962460558826787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6120648639949947411769049 4590486479962460558826787)
        ·
          refine ⟨6885729719943690838240181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4590486479962460558826787 6885729719943690838240181)
          ·
            refine ⟨645537161244721016085017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6885729719943690838240181 645537161244721016085017)
            ·
              refine ⟨484152870933540762063763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 645537161244721016085017 484152870933540762063763)
              ·
                refine ⟨726229306400311143095645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 484152870933540762063763 726229306400311143095645)
                ·
                  refine ⟨272335989900116678660867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 726229306400311143095645 272335989900116678660867)
                  ·
                    rfl

theorem cell20_596669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 2, 1, 3].length) (baseStart_596669 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_596669 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_596669 prefixEnd_596669 := by exact prefixLift 596669
  have htrace : WordTrace (prefixWord ++ tailWord_596669) baseStart_596669 baseEnd_596669 := by
    simpa [prefixWord, tailWord_596669, baseEnd_596669] using wordTrace_append hprefix tailTrace_596669
  have hstable : (prefixWord ++ tailWord_596669).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596669).length < 2 ^ (prefixWord ++ tailWord_596669).sum := by decide
  have hdescent : baseEnd_596669 < baseStart_596669 := by decide
  rcases family_descends (prefixWord ++ tailWord_596669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596697 : List Nat := [1, 2, 1, 2, 3, 2, 2, 5, 2]
def baseStart_596697 : Nat := 118140960795 + 596697 * 2 ^ 59
def prefixEnd_596697 : Nat := 4983230072969 + 3 ^ 40 * 596697 * 2
def baseEnd_596697 : Nat := 272348769863073025727419

theorem tailTrace_596697 : CollatzResearch.WordTrace tailWord_596697 prefixEnd_596697 272348769863073025727419 := by
  unfold tailWord_596697
  simp only [CollatzResearch.WordTrace]
  refine ⟨21763327519276151579420345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14508885012850767719613563 21763327519276151579420345)
  ·
    refine ⟨16322495639457113684565259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21763327519276151579420345 16322495639457113684565259)
    ·
      refine ⟨24483743459185670526847889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16322495639457113684565259 24483743459185670526847889)
      ·
        refine ⟨18362807594389252895135917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24483743459185670526847889 18362807594389252895135917)
        ·
          refine ⟨6886052847895969835675969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18362807594389252895135917 6886052847895969835675969)
          ·
            refine ⟨5164539635921977376756977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6886052847895969835675969 5164539635921977376756977)
            ·
              refine ⟨3873404726941483032567733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5164539635921977376756977 3873404726941483032567733)
              ·
                refine ⟨363131693150764034303225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3873404726941483032567733 363131693150764034303225)
                ·
                  refine ⟨272348769863073025727419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 363131693150764034303225 272348769863073025727419)
                  ·
                    rfl

theorem cell20_596697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 5, 2].length) (baseStart_596697 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_596697 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_596697 prefixEnd_596697 := by exact prefixLift 596697
  have htrace : WordTrace (prefixWord ++ tailWord_596697) baseStart_596697 baseEnd_596697 := by
    simpa [prefixWord, tailWord_596697, baseEnd_596697] using wordTrace_append hprefix tailTrace_596697
  have hstable : (prefixWord ++ tailWord_596697).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596697).length < 2 ^ (prefixWord ++ tailWord_596697).sum := by decide
  have hdescent : baseEnd_596697 < baseStart_596697 := by decide
  rcases family_descends (prefixWord ++ tailWord_596697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596773 : List Nat := [1, 3, 1, 2, 3, 1, 1, 6, 2]
def baseStart_596773 : Nat := 118140960795 + 596773 * 2 ^ 59
def prefixEnd_596773 : Nat := 4983230072969 + 3 ^ 40 * 596773 * 2
def baseEnd_596773 : Nat := 272383458333954539193775

theorem tailTrace_596773 : CollatzResearch.WordTrace tailWord_596773 prefixEnd_596773 272383458333954539193775 := by
  unfold tailWord_596773
  simp only [CollatzResearch.WordTrace]
  refine ⟨21766099467000816559186973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14510732978000544372791315 21766099467000816559186973)
  ·
    refine ⟨8162287300125306209695115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21766099467000816559186973 8162287300125306209695115)
    ·
      refine ⟨12243430950187959314542673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8162287300125306209695115 12243430950187959314542673)
      ·
        refine ⟨9182573212640969485907005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12243430950187959314542673 9182573212640969485907005)
        ·
          refine ⟨3443464954740363557215127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9182573212640969485907005 3443464954740363557215127)
          ·
            refine ⟨5165197432110545335822691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3443464954740363557215127 5165197432110545335822691)
            ·
              refine ⟨7747796148165818003734037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5165197432110545335822691 7747796148165818003734037)
              ·
                refine ⟨363177944445272718925033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7747796148165818003734037 363177944445272718925033)
                ·
                  refine ⟨272383458333954539193775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 363177944445272718925033 272383458333954539193775)
                  ·
                    rfl

theorem cell20_596773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 6, 2].length) (baseStart_596773 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_596773 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_596773 prefixEnd_596773 := by exact prefixLift 596773
  have htrace : WordTrace (prefixWord ++ tailWord_596773) baseStart_596773 baseEnd_596773 := by
    simpa [prefixWord, tailWord_596773, baseEnd_596773] using wordTrace_append hprefix tailTrace_596773
  have hstable : (prefixWord ++ tailWord_596773).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596773).length < 2 ^ (prefixWord ++ tailWord_596773).sum := by decide
  have hdescent : baseEnd_596773 < baseStart_596773 := by decide
  rcases family_descends (prefixWord ++ tailWord_596773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596777 : List Nat := [1, 2, 1, 1, 1, 1, 1, 4, 8]
def baseStart_596777 : Nat := 118140960795 + 596777 * 2 ^ 59
def prefixEnd_596777 : Nat := 4983230072969 + 3 ^ 40 * 596777 * 2
def baseEnd_596777 : Nat := 272385284042948303060425

theorem tailTrace_596777 : CollatzResearch.WordTrace tailWord_596777 prefixEnd_596777 272385284042948303060425 := by
  unfold tailWord_596777
  simp only [CollatzResearch.WordTrace]
  refine ⟨21766245358986325242332585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14510830239324216828221723 21766245358986325242332585)
  ·
    refine ⟨16324684019239743931749439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21766245358986325242332585 16324684019239743931749439)
    ·
      refine ⟨24487026028859615897624159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16324684019239743931749439 24487026028859615897624159)
      ·
        refine ⟨36730539043289423846436239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24487026028859615897624159 36730539043289423846436239)
        ·
          refine ⟨55095808564934135769654359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36730539043289423846436239 55095808564934135769654359)
          ·
            refine ⟨82643712847401203654481539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55095808564934135769654359 82643712847401203654481539)
            ·
              refine ⟨123965569271101805481722309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82643712847401203654481539 123965569271101805481722309)
              ·
                refine ⟨23243544238331588527822933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 123965569271101805481722309 23243544238331588527822933)
                ·
                  refine ⟨272385284042948303060425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23243544238331588527822933 272385284042948303060425)
                  ·
                    rfl

theorem cell20_596777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 8].length) (baseStart_596777 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_596777 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_596777 prefixEnd_596777 := by exact prefixLift 596777
  have htrace : WordTrace (prefixWord ++ tailWord_596777) baseStart_596777 baseEnd_596777 := by
    simpa [prefixWord, tailWord_596777, baseEnd_596777] using wordTrace_append hprefix tailTrace_596777
  have hstable : (prefixWord ++ tailWord_596777).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596777).length < 2 ^ (prefixWord ++ tailWord_596777).sum := by decide
  have hdescent : baseEnd_596777 < baseStart_596777 := by decide
  rcases family_descends (prefixWord ++ tailWord_596777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596808 : List Nat := [2, 1, 3, 1, 1, 3, 1, 1, 7]
def baseStart_596808 : Nat := 118140960795 + 596808 * 2 ^ 59
def prefixEnd_596808 : Nat := 4983230072969 + 3 ^ 40 * 596808 * 2
def baseEnd_596808 : Nat := 272399433287649973026965

theorem tailTrace_596808 : CollatzResearch.WordTrace tailWord_596808 prefixEnd_596808 272399433287649973026965 := by
  unfold tailWord_596808
  simp only [CollatzResearch.WordTrace]
  refine ⟨10883688010937008768355539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14511584014582678357807385 10883688010937008768355539)
  ·
    refine ⟨16325532016405513152533309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10883688010937008768355539 16325532016405513152533309)
    ·
      refine ⟨6122074506152067432199991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16325532016405513152533309 6122074506152067432199991)
      ·
        refine ⟨9183111759228101148299987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6122074506152067432199991 9183111759228101148299987)
        ·
          refine ⟨13774667638842151722449981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9183111759228101148299987 13774667638842151722449981)
          ·
            refine ⟨5165500364565806895918743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13774667638842151722449981 5165500364565806895918743)
            ·
              refine ⟨7748250546848710343878115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5165500364565806895918743 7748250546848710343878115)
              ·
                refine ⟨11622375820273065515817173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7748250546848710343878115 11622375820273065515817173)
                ·
                  refine ⟨272399433287649973026965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11622375820273065515817173 272399433287649973026965)
                  ·
                    rfl

theorem cell20_596808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 7].length) (baseStart_596808 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_596808 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_596808 prefixEnd_596808 := by exact prefixLift 596808
  have htrace : WordTrace (prefixWord ++ tailWord_596808) baseStart_596808 baseEnd_596808 := by
    simpa [prefixWord, tailWord_596808, baseEnd_596808] using wordTrace_append hprefix tailTrace_596808
  have hstable : (prefixWord ++ tailWord_596808).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596808).length < 2 ^ (prefixWord ++ tailWord_596808).sum := by decide
  have hdescent : baseEnd_596808 < baseStart_596808 := by decide
  rcases family_descends (prefixWord ++ tailWord_596808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596828 : List Nat := [2, 2, 4, 2, 1, 3, 1, 1, 4]
def baseStart_596828 : Nat := 118140960795 + 596828 * 2 ^ 59
def prefixEnd_596828 : Nat := 4983230072969 + 3 ^ 40 * 596828 * 2
def baseEnd_596828 : Nat := 272408561832618792360217

theorem tailTrace_596828 : CollatzResearch.WordTrace tailWord_596828 prefixEnd_596828 272408561832618792360217 := by
  unfold tailWord_596828
  simp only [CollatzResearch.WordTrace]
  refine ⟨10884052740900780476219569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14512070321201040634959425 10884052740900780476219569)
  ·
    refine ⟨8163039555675585357164677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10884052740900780476219569 8163039555675585357164677)
    ·
      refine ⟨1530569916689172254468377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8163039555675585357164677 1530569916689172254468377)
      ·
        refine ⟨1147927437516879190851283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1530569916689172254468377 1147927437516879190851283)
        ·
          refine ⟨1721891156275318786276925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1147927437516879190851283 1721891156275318786276925)
          ·
            refine ⟨645709183603244544853847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1721891156275318786276925 645709183603244544853847)
            ·
              refine ⟨968563775404866817280771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 645709183603244544853847 968563775404866817280771)
              ·
                refine ⟨1452845663107300225921157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 968563775404866817280771 1452845663107300225921157)
                ·
                  refine ⟨272408561832618792360217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1452845663107300225921157 272408561832618792360217)
                  ·
                    rfl

theorem cell20_596828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 1, 4].length) (baseStart_596828 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_596828 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_596828 prefixEnd_596828 := by exact prefixLift 596828
  have htrace : WordTrace (prefixWord ++ tailWord_596828) baseStart_596828 baseEnd_596828 := by
    simpa [prefixWord, tailWord_596828, baseEnd_596828] using wordTrace_append hprefix tailTrace_596828
  have hstable : (prefixWord ++ tailWord_596828).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596828).length < 2 ^ (prefixWord ++ tailWord_596828).sum := by decide
  have hdescent : baseEnd_596828 < baseStart_596828 := by decide
  rcases family_descends (prefixWord ++ tailWord_596828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596839 : List Nat := [1, 1, 5, 1, 2, 2, 1, 7]
def baseStart_596839 : Nat := 118140960795 + 596839 * 2 ^ 59
def prefixEnd_596839 : Nat := 4983230072969 + 3 ^ 40 * 596839 * 2
def baseEnd_596839 : Nat := 90804527510783880997835

theorem tailTrace_596839 : CollatzResearch.WordTrace tailWord_596839 prefixEnd_596839 90804527510783880997835 := by
  unfold tailWord_596839
  simp only [CollatzResearch.WordTrace]
  refine ⟨21768506684761709831089571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14512337789841139887393047 21768506684761709831089571)
  ·
    refine ⟨32652760027142564746634357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21768506684761709831089571 32652760027142564746634357)
    ·
      refine ⟨3061196252544615444996971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32652760027142564746634357 3061196252544615444996971)
      ·
        refine ⟨4591794378816923167495457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3061196252544615444996971 4591794378816923167495457)
        ·
          refine ⟨3443845784112692375621593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4591794378816923167495457 3443845784112692375621593)
          ·
            refine ⟨2582884338084519281716195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3443845784112692375621593 2582884338084519281716195)
            ·
              refine ⟨3874326507126778922574293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2582884338084519281716195 3874326507126778922574293)
              ·
                refine ⟨90804527510783880997835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3874326507126778922574293 90804527510783880997835)
                ·
                  rfl

theorem cell20_596839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 7].length) (baseStart_596839 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_596839 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_596839 prefixEnd_596839 := by exact prefixLift 596839
  have htrace : WordTrace (prefixWord ++ tailWord_596839) baseStart_596839 baseEnd_596839 := by
    simpa [prefixWord, tailWord_596839, baseEnd_596839] using wordTrace_append hprefix tailTrace_596839
  have hstable : (prefixWord ++ tailWord_596839).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596839).length < 2 ^ (prefixWord ++ tailWord_596839).sum := by decide
  have hdescent : baseEnd_596839 < baseStart_596839 := by decide
  rcases family_descends (prefixWord ++ tailWord_596839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596887 : List Nat := [1, 1, 3, 3, 1, 2, 3, 4, 2]
def baseStart_596887 : Nat := 118140960795 + 596887 * 2 ^ 59
def prefixEnd_596887 : Nat := 4983230072969 + 3 ^ 40 * 596887 * 2
def baseEnd_596887 : Nat := 272435491040276809393309

theorem tailTrace_596887 : CollatzResearch.WordTrace tailWord_596887 prefixEnd_596887 272435491040276809393309 := by
  unfold tailWord_596887
  simp only [CollatzResearch.WordTrace]
  refine ⟨21770257388587814028836915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14513504925725209352557943 21770257388587814028836915)
  ·
    refine ⟨32655386082881721043255373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21770257388587814028836915 32655386082881721043255373)
    ·
      refine ⟨12245769781080645391220765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32655386082881721043255373 12245769781080645391220765)
      ·
        refine ⟨4592163667905242021707787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12245769781080645391220765 4592163667905242021707787)
        ·
          refine ⟨6888245501857863032561681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4592163667905242021707787 6888245501857863032561681)
          ·
            refine ⟨5166184126393397274421261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6888245501857863032561681 5166184126393397274421261)
            ·
              refine ⟨1937319047397523977907973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5166184126393397274421261 1937319047397523977907973)
              ·
                refine ⟨363247321387035745857745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1937319047397523977907973 363247321387035745857745)
                ·
                  refine ⟨272435491040276809393309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 363247321387035745857745 272435491040276809393309)
                  ·
                    rfl

theorem cell20_596887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 4, 2].length) (baseStart_596887 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_596887 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_596887 prefixEnd_596887 := by exact prefixLift 596887
  have htrace : WordTrace (prefixWord ++ tailWord_596887) baseStart_596887 baseEnd_596887 := by
    simpa [prefixWord, tailWord_596887, baseEnd_596887] using wordTrace_append hprefix tailTrace_596887
  have hstable : (prefixWord ++ tailWord_596887).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596887).length < 2 ^ (prefixWord ++ tailWord_596887).sum := by decide
  have hdescent : baseEnd_596887 < baseStart_596887 := by decide
  rcases family_descends (prefixWord ++ tailWord_596887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596922 : List Nat := [3, 1, 1, 1, 2, 1, 4, 2, 5]
def baseStart_596922 : Nat := 118140960795 + 596922 * 2 ^ 59
def prefixEnd_596922 : Nat := 4983230072969 + 3 ^ 40 * 596922 * 2
def baseEnd_596922 : Nat := 272451465993972243226499

theorem tailTrace_596922 : CollatzResearch.WordTrace tailWord_596922 prefixEnd_596922 272451465993972243226499 := by
  unfold tailWord_596922
  simp only [CollatzResearch.WordTrace]
  refine ⟨5442883485865253751590255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14514355962307343337574013 5442883485865253751590255)
  ·
    refine ⟨8164325228797880627385383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5442883485865253751590255 8164325228797880627385383)
    ·
      refine ⟨12246487843196820941078075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8164325228797880627385383 12246487843196820941078075)
      ·
        refine ⟨18369731764795231411617113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12246487843196820941078075 18369731764795231411617113)
        ·
          refine ⟨13777298823596423558712835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18369731764795231411617113 13777298823596423558712835)
          ·
            refine ⟨20665948235394635338069253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13777298823596423558712835 20665948235394635338069253)
            ·
              refine ⟨3874865294136494125887985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20665948235394635338069253 3874865294136494125887985)
              ·
                refine ⟨2906148970602370594415989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3874865294136494125887985 2906148970602370594415989)
                ·
                  refine ⟨272451465993972243226499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2906148970602370594415989 272451465993972243226499)
                  ·
                    rfl

theorem cell20_596922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_596922 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_596922 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_596922 prefixEnd_596922 := by exact prefixLift 596922
  have htrace : WordTrace (prefixWord ++ tailWord_596922) baseStart_596922 baseEnd_596922 := by
    simpa [prefixWord, tailWord_596922, baseEnd_596922] using wordTrace_append hprefix tailTrace_596922
  have hstable : (prefixWord ++ tailWord_596922).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596922).length < 2 ^ (prefixWord ++ tailWord_596922).sum := by decide
  have hdescent : baseEnd_596922 < baseStart_596922 := by decide
  rcases family_descends (prefixWord ++ tailWord_596922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596939 : List Nat := [1, 1, 1, 1, 3, 5, 3, 2, 3]
def baseStart_596939 : Nat := 118140960795 + 596939 * 2 ^ 59
def prefixEnd_596939 : Nat := 4983230072969 + 3 ^ 40 * 596939 * 2
def baseEnd_596939 : Nat := 272459225257195739659763

theorem tailTrace_596939 : CollatzResearch.WordTrace tailWord_596939 prefixEnd_596939 272459225257195739659763 := by
  unfold tailWord_596939
  simp only [CollatzResearch.WordTrace]
  refine ⟨21772153984399426909729871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14514769322932951273153247 21772153984399426909729871)
  ·
    refine ⟨32658230976599140364594807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21772153984399426909729871 32658230976599140364594807)
    ·
      refine ⟨48987346464898710546892211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32658230976599140364594807 48987346464898710546892211)
      ·
        refine ⟨73481019697348065820338317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48987346464898710546892211 73481019697348065820338317)
        ·
          refine ⟨27555382386505524682626869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73481019697348065820338317 27555382386505524682626869)
          ·
            refine ⟨2583317098734892938996269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27555382386505524682626869 2583317098734892938996269)
            ·
              refine ⟨968743912025584852123601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2583317098734892938996269 968743912025584852123601)
              ·
                refine ⟨726557934019188639092701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 968743912025584852123601 726557934019188639092701)
                ·
                  refine ⟨272459225257195739659763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 726557934019188639092701 272459225257195739659763)
                  ·
                    rfl

theorem cell20_596939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 2, 3].length) (baseStart_596939 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_596939 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_596939 prefixEnd_596939 := by exact prefixLift 596939
  have htrace : WordTrace (prefixWord ++ tailWord_596939) baseStart_596939 baseEnd_596939 := by
    simpa [prefixWord, tailWord_596939, baseEnd_596939] using wordTrace_append hprefix tailTrace_596939
  have hstable : (prefixWord ++ tailWord_596939).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596939).length < 2 ^ (prefixWord ++ tailWord_596939).sum := by decide
  have hdescent : baseEnd_596939 < baseStart_596939 := by decide
  rcases family_descends (prefixWord ++ tailWord_596939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_596970 : List Nat := [3, 1, 3, 1, 2, 2, 4, 4]
def baseStart_596970 : Nat := 118140960795 + 596970 * 2 ^ 59
def prefixEnd_596970 : Nat := 4983230072969 + 3 ^ 40 * 596970 * 2
def baseEnd_596970 : Nat := 90824458167299136542101

theorem tailTrace_596970 : CollatzResearch.WordTrace tailWord_596970 prefixEnd_596970 90824458167299136542101 := by
  unfold tailWord_596970
  simp only [CollatzResearch.WordTrace]
  refine ⟨5443321161821779801027091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14515523098191412802738909 5443321161821779801027091)
  ·
    refine ⟨8164981742732669701540637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5443321161821779801027091 8164981742732669701540637)
    ·
      refine ⟨3061868153524751138077739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8164981742732669701540637 3061868153524751138077739)
      ·
        refine ⟨4592802230287126707116609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3061868153524751138077739 4592802230287126707116609)
        ·
          refine ⟨3444601672715345030337457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4592802230287126707116609 3444601672715345030337457)
          ·
            refine ⟨2583451254536508772753093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3444601672715345030337457 2583451254536508772753093)
            ·
              refine ⟨484397110225595394891205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2583451254536508772753093 484397110225595394891205)
              ·
                refine ⟨90824458167299136542101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 484397110225595394891205 90824458167299136542101)
                ·
                  rfl

theorem cell20_596970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 4, 4].length) (baseStart_596970 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_596970 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_596970 prefixEnd_596970 := by exact prefixLift 596970
  have htrace : WordTrace (prefixWord ++ tailWord_596970) baseStart_596970 baseEnd_596970 := by
    simpa [prefixWord, tailWord_596970, baseEnd_596970] using wordTrace_append hprefix tailTrace_596970
  have hstable : (prefixWord ++ tailWord_596970).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_596970).length < 2 ^ (prefixWord ++ tailWord_596970).sum := by decide
  have hdescent : baseEnd_596970 < baseStart_596970 := by decide
  rcases family_descends (prefixWord ++ tailWord_596970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597053 : List Nat := [1, 4, 1, 3, 1, 2, 1, 4, 3]
def baseStart_597053 : Nat := 118140960795 + 597053 * 2 ^ 59
def prefixEnd_597053 : Nat := 4983230072969 + 3 ^ 40 * 597053 * 2
def baseEnd_597053 : Nat := 272511257963518009859297

theorem tailTrace_597053 : CollatzResearch.WordTrace tailWord_597053 prefixEnd_597053 272511257963518009859297 := by
  unfold tailWord_597053
  simp only [CollatzResearch.WordTrace]
  refine ⟨21776311905986424379379813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14517541270657616252919875 21776311905986424379379813)
  ·
    refine ⟨4083058482372454571133715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21776311905986424379379813 4083058482372454571133715)
    ·
      refine ⟨6124587723558681856700573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4083058482372454571133715 6124587723558681856700573)
      ·
        refine ⟨2296720396334505696262715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6124587723558681856700573 2296720396334505696262715)
        ·
          refine ⟨3445080594501758544394073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2296720396334505696262715 3445080594501758544394073)
          ·
            refine ⟨2583810445876318908295555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3445080594501758544394073 2583810445876318908295555)
            ·
              refine ⟨3875715668814478362443333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2583810445876318908295555 3875715668814478362443333)
              ·
                refine ⟨726696687902714692958125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3875715668814478362443333 726696687902714692958125)
                ·
                  refine ⟨272511257963518009859297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 726696687902714692958125 272511257963518009859297)
                  ·
                    rfl

theorem cell20_597053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 4, 3].length) (baseStart_597053 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_597053 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_597053 prefixEnd_597053 := by exact prefixLift 597053
  have htrace : WordTrace (prefixWord ++ tailWord_597053) baseStart_597053 baseEnd_597053 := by
    simpa [prefixWord, tailWord_597053, baseEnd_597053] using wordTrace_append hprefix tailTrace_597053
  have hstable : (prefixWord ++ tailWord_597053).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597053).length < 2 ^ (prefixWord ++ tailWord_597053).sum := by decide
  have hdescent : baseEnd_597053 < baseStart_597053 := by decide
  rcases family_descends (prefixWord ++ tailWord_597053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597084 : List Nat := [2, 2, 4, 1, 1, 1, 5, 4]
def baseStart_597084 : Nat := 118140960795 + 597084 * 2 ^ 59
def prefixEnd_597084 : Nat := 4983230072969 + 3 ^ 40 * 597084 * 2
def baseEnd_597084 : Nat := 90841802402739893275279

theorem tailTrace_597084 : CollatzResearch.WordTrace tailWord_597084 prefixEnd_597084 90841802402739893275279 := by
  unfold tailWord_597084
  simp only [CollatzResearch.WordTrace]
  refine ⟨10888721284437058336879153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14518295045916077782505537 10888721284437058336879153)
  ·
    refine ⟨8166540963327793752659365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10888721284437058336879153 8166540963327793752659365)
    ·
      refine ⟨1531226430623961328623631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8166540963327793752659365 1531226430623961328623631)
      ·
        refine ⟨2296839645935941992935447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1531226430623961328623631 2296839645935941992935447)
        ·
          refine ⟨3445259468903912989403171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2296839645935941992935447 3445259468903912989403171)
          ·
            refine ⟨5167889203355869484104757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3445259468903912989403171 5167889203355869484104757)
            ·
              refine ⟨484489612814612764134821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5167889203355869484104757 484489612814612764134821)
              ·
                refine ⟨90841802402739893275279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 484489612814612764134821 90841802402739893275279)
                ·
                  rfl

theorem cell20_597084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 5, 4].length) (baseStart_597084 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_597084 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_597084 prefixEnd_597084 := by exact prefixLift 597084
  have htrace : WordTrace (prefixWord ++ tailWord_597084) baseStart_597084 baseEnd_597084 := by
    simpa [prefixWord, tailWord_597084, baseEnd_597084] using wordTrace_append hprefix tailTrace_597084
  have hstable : (prefixWord ++ tailWord_597084).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597084).length < 2 ^ (prefixWord ++ tailWord_597084).sum := by decide
  have hdescent : baseEnd_597084 < baseStart_597084 := by decide
  rcases family_descends (prefixWord ++ tailWord_597084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597143 : List Nat := [1, 1, 3, 3, 3, 2, 1, 6]
def baseStart_597143 : Nat := 118140960795 + 597143 * 2 ^ 59
def prefixEnd_597143 : Nat := 4983230072969 + 3 ^ 40 * 597143 * 2
def baseEnd_597143 : Nat := 90850778805292565619643

theorem tailTrace_597143 : CollatzResearch.WordTrace tailWord_597143 prefixEnd_597143 90850778805292565619643 := by
  unfold tailWord_597143
  simp only [CollatzResearch.WordTrace]
  refine ⟨21779594475660369750156083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14519729650440246500104055 21779594475660369750156083)
  ·
    refine ⟨32669391713490554625234125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21779594475660369750156083 32669391713490554625234125)
    ·
      refine ⟨12251021892558957984462797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32669391713490554625234125 12251021892558957984462797)
      ·
        refine ⟨4594133209709609244173549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12251021892558957984462797 4594133209709609244173549)
        ·
          refine ⟨1722799953641103466565081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4594133209709609244173549 1722799953641103466565081)
          ·
            refine ⟨1292099965230827599923811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1722799953641103466565081 1292099965230827599923811)
            ·
              refine ⟨1938149947846241399885717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1292099965230827599923811 1938149947846241399885717)
              ·
                refine ⟨90850778805292565619643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1938149947846241399885717 90850778805292565619643)
                ·
                  rfl

theorem cell20_597143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 6].length) (baseStart_597143 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_597143 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_597143 prefixEnd_597143 := by exact prefixLift 597143
  have htrace : WordTrace (prefixWord ++ tailWord_597143) baseStart_597143 baseEnd_597143 := by
    simpa [prefixWord, tailWord_597143, baseEnd_597143] using wordTrace_append hprefix tailTrace_597143
  have hstable : (prefixWord ++ tailWord_597143).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597143).length < 2 ^ (prefixWord ++ tailWord_597143).sum := by decide
  have hdescent : baseEnd_597143 < baseStart_597143 := by decide
  rcases family_descends (prefixWord ++ tailWord_597143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597170 : List Nat := [3, 2, 1, 1, 1, 5, 3, 2, 2]
def baseStart_597170 : Nat := 118140960795 + 597170 * 2 ^ 59
def prefixEnd_597170 : Nat := 4983230072969 + 3 ^ 40 * 597170 * 2
def baseEnd_597170 : Nat := 272564659951585602958819

theorem tailTrace_597170 : CollatzResearch.WordTrace tailWord_597170 prefixEnd_597170 272564659951585602958819 := by
  unfold tailWord_597170
  simp only [CollatzResearch.WordTrace]
  refine ⟨5445144811640638340347241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14520386164375035574259309 5445144811640638340347241)
  ·
    refine ⟨4083858608730478755260431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5445144811640638340347241 4083858608730478755260431)
    ·
      refine ⟨6125787913095718132890647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4083858608730478755260431 6125787913095718132890647)
      ·
        refine ⟨9188681869643577199335971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6125787913095718132890647 9188681869643577199335971)
        ·
          refine ⟨13783022804465365799003957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9188681869643577199335971 13783022804465365799003957)
          ·
            refine ⟨1292158387918628043656621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13783022804465365799003957 1292158387918628043656621)
            ·
              refine ⟨484559395469485516371233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1292158387918628043656621 484559395469485516371233)
              ·
                refine ⟨363419546602114137278425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 484559395469485516371233 363419546602114137278425)
                ·
                  refine ⟨272564659951585602958819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 363419546602114137278425 272564659951585602958819)
                  ·
                    rfl

theorem cell20_597170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 3, 2, 2].length) (baseStart_597170 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_597170 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_597170 prefixEnd_597170 := by exact prefixLift 597170
  have htrace : WordTrace (prefixWord ++ tailWord_597170) baseStart_597170 baseEnd_597170 := by
    simpa [prefixWord, tailWord_597170, baseEnd_597170] using wordTrace_append hprefix tailTrace_597170
  have hstable : (prefixWord ++ tailWord_597170).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597170).length < 2 ^ (prefixWord ++ tailWord_597170).sum := by decide
  have hdescent : baseEnd_597170 < baseStart_597170 := by decide
  rcases family_descends (prefixWord ++ tailWord_597170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597233 : List Nat := [1, 2, 2, 2, 2, 1, 1, 5, 4]
def baseStart_597233 : Nat := 118140960795 + 597233 * 2 ^ 59
def prefixEnd_597233 : Nat := 4983230072969 + 3 ^ 40 * 597233 * 2
def baseEnd_597233 : Nat := 272593414868237383858561

theorem tailTrace_597233 : CollatzResearch.WordTrace tailWord_597233 prefixEnd_597233 272593414868237383858561 := by
  unfold tailWord_597233
  simp only [CollatzResearch.WordTrace]
  refine ⟨21782877045334315120932353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14521918030222876747288235 21782877045334315120932353)
  ·
    refine ⟨16337157784000736340699265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21782877045334315120932353 16337157784000736340699265)
    ·
      refine ⟨12252868338000552255524449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16337157784000736340699265 12252868338000552255524449)
      ·
        refine ⟨9189651253500414191643337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12252868338000552255524449 9189651253500414191643337)
        ·
          refine ⟨6892238440125310643732503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9189651253500414191643337 6892238440125310643732503)
          ·
            refine ⟨10338357660187965965598755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6892238440125310643732503 10338357660187965965598755)
            ·
              refine ⟨15507536490281948948398133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10338357660187965965598755 15507536490281948948398133)
              ·
                refine ⟨1453831545963932713912325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15507536490281948948398133 1453831545963932713912325)
                ·
                  refine ⟨272593414868237383858561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1453831545963932713912325 272593414868237383858561)
                  ·
                    rfl

theorem cell20_597233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 5, 4].length) (baseStart_597233 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_597233 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_597233 prefixEnd_597233 := by exact prefixLift 597233
  have htrace : WordTrace (prefixWord ++ tailWord_597233) baseStart_597233 baseEnd_597233 := by
    simpa [prefixWord, tailWord_597233, baseEnd_597233] using wordTrace_append hprefix tailTrace_597233
  have hstable : (prefixWord ++ tailWord_597233).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597233).length < 2 ^ (prefixWord ++ tailWord_597233).sum := by decide
  have hdescent : baseEnd_597233 < baseStart_597233 := by decide
  rcases family_descends (prefixWord ++ tailWord_597233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597257 : List Nat := [1, 2, 1, 1, 3, 3, 5, 4]
def baseStart_597257 : Nat := 118140960795 + 597257 * 2 ^ 59
def prefixEnd_597257 : Nat := 4983230072969 + 3 ^ 40 * 597257 * 2
def baseEnd_597257 : Nat := 90868123040733322352821

theorem tailTrace_597257 : CollatzResearch.WordTrace tailWord_597257 prefixEnd_597257 90868123040733322352821 := by
  unfold tailWord_597257
  simp only [CollatzResearch.WordTrace]
  refine ⟨21783752397247367219806025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14522501598164911479870683 21783752397247367219806025)
  ·
    refine ⟨16337814297935525414854519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21783752397247367219806025 16337814297935525414854519)
    ·
      refine ⟨24506721446903288122281779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16337814297935525414854519 24506721446903288122281779)
      ·
        refine ⟨36760082170354932183422669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24506721446903288122281779 36760082170354932183422669)
        ·
          refine ⟨13785030813883099568783501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36760082170354932183422669 13785030813883099568783501)
          ·
            refine ⟨5169386555206162338293813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13785030813883099568783501 5169386555206162338293813)
            ·
              refine ⟨484629989550577719215045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5169386555206162338293813 484629989550577719215045)
              ·
                refine ⟨90868123040733322352821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 484629989550577719215045 90868123040733322352821)
                ·
                  rfl

theorem cell20_597257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 5, 4].length) (baseStart_597257 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_597257 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_597257 prefixEnd_597257 := by exact prefixLift 597257
  have htrace : WordTrace (prefixWord ++ tailWord_597257) baseStart_597257 baseEnd_597257 := by
    simpa [prefixWord, tailWord_597257, baseEnd_597257] using wordTrace_append hprefix tailTrace_597257
  have hstable : (prefixWord ++ tailWord_597257).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597257).length < 2 ^ (prefixWord ++ tailWord_597257).sum := by decide
  have hdescent : baseEnd_597257 < baseStart_597257 := by decide
  rcases family_descends (prefixWord ++ tailWord_597257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597271 : List Nat := [1, 1, 3, 4, 1, 1, 1, 2, 6]
def baseStart_597271 : Nat := 118140960795 + 597271 * 2 ^ 59
def prefixEnd_597271 : Nat := 4983230072969 + 3 ^ 40 * 597271 * 2
def baseEnd_597271 : Nat := 272610759103678140591739

theorem tailTrace_597271 : CollatzResearch.WordTrace tailWord_597271 prefixEnd_597271 272610759103678140591739 := by
  unfold tailWord_597271
  simp only [CollatzResearch.WordTrace]
  refine ⟨21784263019196647610815667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14522842012797765073877111 21784263019196647610815667)
  ·
    refine ⟨32676394528794971416223501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21784263019196647610815667 32676394528794971416223501)
    ·
      refine ⟨12253647948298114281083813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32676394528794971416223501 12253647948298114281083813)
      ·
        refine ⟨2297558990305896427703215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12253647948298114281083813 2297558990305896427703215)
        ·
          refine ⟨3446338485458844641554823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2297558990305896427703215 3446338485458844641554823)
          ·
            refine ⟨5169507728188266962332235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3446338485458844641554823 5169507728188266962332235)
            ·
              refine ⟨7754261592282400443498353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5169507728188266962332235 7754261592282400443498353)
              ·
                refine ⟨5815696194211800332623765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7754261592282400443498353 5815696194211800332623765)
                ·
                  refine ⟨272610759103678140591739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5815696194211800332623765 272610759103678140591739)
                  ·
                    rfl

theorem cell20_597271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 6].length) (baseStart_597271 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_597271 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_597271 prefixEnd_597271 := by exact prefixLift 597271
  have htrace : WordTrace (prefixWord ++ tailWord_597271) baseStart_597271 baseEnd_597271 := by
    simpa [prefixWord, tailWord_597271, baseEnd_597271] using wordTrace_append hprefix tailTrace_597271
  have hstable : (prefixWord ++ tailWord_597271).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597271).length < 2 ^ (prefixWord ++ tailWord_597271).sum := by decide
  have hdescent : baseEnd_597271 < baseStart_597271 := by decide
  rcases family_descends (prefixWord ++ tailWord_597271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597288 : List Nat := [2, 1, 5, 1, 2, 1, 1, 3, 4]
def baseStart_597288 : Nat := 118140960795 + 597288 * 2 ^ 59
def prefixEnd_597288 : Nat := 4983230072969 + 3 ^ 40 * 597288 * 2
def baseEnd_597288 : Nat := 272618518366901637025003

theorem tailTrace_597288 : CollatzResearch.WordTrace tailWord_597288 prefixEnd_597288 272618518366901637025003 := by
  unfold tailWord_597288
  simp only [CollatzResearch.WordTrace]
  refine ⟨10892441530067529757092259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14523255373423373009456345 10892441530067529757092259)
  ·
    refine ⟨16338662295101294635638389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10892441530067529757092259 16338662295101294635638389)
    ·
      refine ⟨1531749590165746372091099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16338662295101294635638389 1531749590165746372091099)
      ·
        refine ⟨2297624385248619558136649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1531749590165746372091099 2297624385248619558136649)
        ·
          refine ⟨1723218288936464668602487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2297624385248619558136649 1723218288936464668602487)
          ·
            refine ⟨2584827433404697002903731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1723218288936464668602487 2584827433404697002903731)
            ·
              refine ⟨3877241150107045504355597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2584827433404697002903731 3877241150107045504355597)
              ·
                refine ⟨1453965431290142064133349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3877241150107045504355597 1453965431290142064133349)
                ·
                  refine ⟨272618518366901637025003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1453965431290142064133349 272618518366901637025003)
                  ·
                    rfl

theorem cell20_597288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 3, 4].length) (baseStart_597288 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_597288 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_597288 prefixEnd_597288 := by exact prefixLift 597288
  have htrace : WordTrace (prefixWord ++ tailWord_597288) baseStart_597288 baseEnd_597288 := by
    simpa [prefixWord, tailWord_597288, baseEnd_597288] using wordTrace_append hprefix tailTrace_597288
  have hstable : (prefixWord ++ tailWord_597288).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597288).length < 2 ^ (prefixWord ++ tailWord_597288).sum := by decide
  have hdescent : baseEnd_597288 < baseStart_597288 := by decide
  rcases family_descends (prefixWord ++ tailWord_597288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597298 : List Nat := [3, 2, 1, 1, 4, 2, 3, 1, 3]
def baseStart_597298 : Nat := 118140960795 + 597298 * 2 ^ 59
def prefixEnd_597298 : Nat := 4983230072969 + 3 ^ 40 * 597298 * 2
def baseEnd_597298 : Nat := 272623082639386046691629

theorem tailTrace_597298 : CollatzResearch.WordTrace tailWord_597298 prefixEnd_597298 272623082639386046691629 := by
  unfold tailWord_597298
  simp only [CollatzResearch.WordTrace]
  refine ⟨5446311947524707805512137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14523498526732554148032365 5446311947524707805512137)
  ·
    refine ⟨4084733960643530854134103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5446311947524707805512137 4084733960643530854134103)
    ·
      refine ⟨6127100940965296281201155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4084733960643530854134103 6127100940965296281201155)
      ·
        refine ⟨9190651411447944421801733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6127100940965296281201155 9190651411447944421801733)
        ·
          refine ⟨1723247139646489579087825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9190651411447944421801733 1723247139646489579087825)
          ·
            refine ⟨1292435354734867184315869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1723247139646489579087825 1292435354734867184315869)
            ·
              refine ⟨484663258025575194118451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1292435354734867184315869 484663258025575194118451)
              ·
                refine ⟨726994887038362791177677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 484663258025575194118451 726994887038362791177677)
                ·
                  refine ⟨272623082639386046691629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 726994887038362791177677 272623082639386046691629)
                  ·
                    rfl

theorem cell20_597298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 3, 1, 3].length) (baseStart_597298 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_597298 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_597298 prefixEnd_597298 := by exact prefixLift 597298
  have htrace : WordTrace (prefixWord ++ tailWord_597298) baseStart_597298 baseEnd_597298 := by
    simpa [prefixWord, tailWord_597298, baseEnd_597298] using wordTrace_append hprefix tailTrace_597298
  have hstable : (prefixWord ++ tailWord_597298).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597298).length < 2 ^ (prefixWord ++ tailWord_597298).sum := by decide
  have hdescent : baseEnd_597298 < baseStart_597298 := by decide
  rcases family_descends (prefixWord ++ tailWord_597298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597333 : List Nat := [1, 3, 2, 2, 3, 3, 6]
def baseStart_597333 : Nat := 118140960795 + 597333 * 2 ^ 59
def prefixEnd_597333 : Nat := 4983230072969 + 3 ^ 40 * 597333 * 2
def baseEnd_597333 : Nat := 30293228621453497836091

theorem tailTrace_597333 : CollatzResearch.WordTrace tailWord_597333 prefixEnd_597333 30293228621453497836091 := by
  unfold tailWord_597333
  simp only [CollatzResearch.WordTrace]
  refine ⟨21786524344972032199572653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14524349563314688133048435 21786524344972032199572653)
  ·
    refine ⟨8169946629364512074839745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21786524344972032199572653 8169946629364512074839745)
    ·
      refine ⟨6127459972023384056129809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8169946629364512074839745 6127459972023384056129809)
      ·
        refine ⟨4595594979017538042097357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6127459972023384056129809 4595594979017538042097357)
        ·
          refine ⟨1723348117131576765786509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4595594979017538042097357 1723348117131576765786509)
          ·
            refine ⟨646255543924341287169941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1723348117131576765786509 646255543924341287169941)
            ·
              refine ⟨30293228621453497836091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 646255543924341287169941 30293228621453497836091)
              ·
                rfl

theorem cell20_597333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 6].length) (baseStart_597333 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_597333 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_597333 prefixEnd_597333 := by exact prefixLift 597333
  have htrace : WordTrace (prefixWord ++ tailWord_597333) baseStart_597333 baseEnd_597333 := by
    simpa [prefixWord, tailWord_597333, baseEnd_597333] using wordTrace_append hprefix tailTrace_597333
  have hstable : (prefixWord ++ tailWord_597333).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597333).length < 2 ^ (prefixWord ++ tailWord_597333).sum := by decide
  have hdescent : baseEnd_597333 < baseStart_597333 := by decide
  rcases family_descends (prefixWord ++ tailWord_597333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597357 : List Nat := [1, 5, 1, 1, 1, 4, 1, 3, 3]
def baseStart_597357 : Nat := 118140960795 + 597357 * 2 ^ 59
def prefixEnd_597357 : Nat := 4983230072969 + 3 ^ 40 * 597357 * 2
def baseEnd_597357 : Nat := 272650011847044063724721

theorem tailTrace_597357 : CollatzResearch.WordTrace tailWord_597357 prefixEnd_597357 272650011847044063724721 := by
  unfold tailWord_597357
  simp only [CollatzResearch.WordTrace]
  refine ⟨21787399696885084298446325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14524933131256722865630883 21787399696885084298446325)
  ·
    refine ⟨2042568721582976652979343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21787399696885084298446325 2042568721582976652979343)
    ·
      refine ⟨3063853082374464979469015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2042568721582976652979343 3063853082374464979469015)
      ·
        refine ⟨4595779623561697469203523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3063853082374464979469015 4595779623561697469203523)
        ·
          refine ⟨6893669435342546203805285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4595779623561697469203523 6893669435342546203805285)
          ·
            refine ⟨1292563019126727413213491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6893669435342546203805285 1292563019126727413213491)
            ·
              refine ⟨1938844528690091119820237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1292563019126727413213491 1938844528690091119820237)
              ·
                refine ⟨727066698258784169932589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1938844528690091119820237 727066698258784169932589)
                ·
                  refine ⟨272650011847044063724721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 727066698258784169932589 272650011847044063724721)
                  ·
                    rfl

theorem cell20_597357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_597357 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_597357 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_597357 prefixEnd_597357 := by exact prefixLift 597357
  have htrace : WordTrace (prefixWord ++ tailWord_597357) baseStart_597357 baseEnd_597357 := by
    simpa [prefixWord, tailWord_597357, baseEnd_597357] using wordTrace_append hprefix tailTrace_597357
  have hstable : (prefixWord ++ tailWord_597357).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597357).length < 2 ^ (prefixWord ++ tailWord_597357).sum := by decide
  have hdescent : baseEnd_597357 < baseStart_597357 := by decide
  rcases family_descends (prefixWord ++ tailWord_597357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597394 : List Nat := [3, 2, 3, 3, 1, 2, 2, 2, 2]
def baseStart_597394 : Nat := 118140960795 + 597394 * 2 ^ 59
def prefixEnd_597394 : Nat := 4983230072969 + 3 ^ 40 * 597394 * 2
def baseEnd_597394 : Nat := 272666899655236379491237

theorem tailTrace_597394 : CollatzResearch.WordTrace tailWord_597394 prefixEnd_597394 272666899655236379491237 := by
  unfold tailWord_597394
  simp only [CollatzResearch.WordTrace]
  refine ⟨5447187299437759904385809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14525832798500693078362157 5447187299437759904385809)
  ·
    refine ⟨4085390474578319928289357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5447187299437759904385809 4085390474578319928289357)
    ·
      refine ⟨1532021427966869973108509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4085390474578319928289357 1532021427966869973108509)
      ·
        refine ⟨574508035487576239915691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1532021427966869973108509 574508035487576239915691)
        ·
          refine ⟨861762053231364359873537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 574508035487576239915691 861762053231364359873537)
          ·
            refine ⟨646321539923523269905153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 861762053231364359873537 646321539923523269905153)
            ·
              refine ⟨484741154942642452428865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 646321539923523269905153 484741154942642452428865)
              ·
                refine ⟨363555866206981839321649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 484741154942642452428865 363555866206981839321649)
                ·
                  refine ⟨272666899655236379491237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 363555866206981839321649 272666899655236379491237)
                  ·
                    rfl

theorem cell20_597394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 2, 2, 2].length) (baseStart_597394 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_597394 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_597394 prefixEnd_597394 := by exact prefixLift 597394
  have htrace : WordTrace (prefixWord ++ tailWord_597394) baseStart_597394 baseEnd_597394 := by
    simpa [prefixWord, tailWord_597394, baseEnd_597394] using wordTrace_append hprefix tailTrace_597394
  have hstable : (prefixWord ++ tailWord_597394).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597394).length < 2 ^ (prefixWord ++ tailWord_597394).sum := by decide
  have hdescent : baseEnd_597394 < baseStart_597394 := by decide
  rcases family_descends (prefixWord ++ tailWord_597394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597436 : List Nat := [2, 2, 2, 4, 2, 1, 2, 3, 2]
def baseStart_597436 : Nat := 118140960795 + 597436 * 2 ^ 59
def prefixEnd_597436 : Nat := 4983230072969 + 3 ^ 40 * 597436 * 2
def baseEnd_597436 : Nat := 272686069599670900091065

theorem tailTrace_597436 : CollatzResearch.WordTrace tailWord_597436 prefixEnd_597436 272686069599670900091065 := by
  unfold tailWord_597436
  simp only [CollatzResearch.WordTrace]
  refine ⟨10895140531799440395286081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14526854042399253860381441 10895140531799440395286081)
  ·
    refine ⟨8171355398849580296464561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10895140531799440395286081 8171355398849580296464561)
    ·
      refine ⟨6128516549137185222348421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8171355398849580296464561 6128516549137185222348421)
      ·
        refine ⟨1149096852963222229190329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6128516549137185222348421 1149096852963222229190329)
        ·
          refine ⟨861822639722416671892747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1149096852963222229190329 861822639722416671892747)
          ·
            refine ⟨1292733959583625007839121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 861822639722416671892747 1292733959583625007839121)
            ·
              refine ⟨969550469687718755879341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1292733959583625007839121 969550469687718755879341)
              ·
                refine ⟨363581426132894533454753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 969550469687718755879341 363581426132894533454753)
                ·
                  refine ⟨272686069599670900091065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 363581426132894533454753 272686069599670900091065)
                  ·
                    rfl

theorem cell20_597436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 3, 2].length) (baseStart_597436 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_597436 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_597436 prefixEnd_597436 := by exact prefixLift 597436
  have htrace : WordTrace (prefixWord ++ tailWord_597436) baseStart_597436 baseEnd_597436 := by
    simpa [prefixWord, tailWord_597436, baseEnd_597436] using wordTrace_append hprefix tailTrace_597436
  have hstable : (prefixWord ++ tailWord_597436).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597436).length < 2 ^ (prefixWord ++ tailWord_597436).sum := by decide
  have hdescent : baseEnd_597436 < baseStart_597436 := by decide
  rcases family_descends (prefixWord ++ tailWord_597436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597440 : List Nat := [2, 1, 1, 2, 3, 1, 3, 5, 2]
def baseStart_597440 : Nat := 118140960795 + 597440 * 2 ^ 59
def prefixEnd_597440 : Nat := 4983230072969 + 3 ^ 40 * 597440 * 2
def baseEnd_597440 : Nat := 272687895308664663957715

theorem tailTrace_597440 : CollatzResearch.WordTrace tailWord_597440 prefixEnd_597440 272687895308664663957715 := by
  unfold tailWord_597440
  simp only [CollatzResearch.WordTrace]
  refine ⟨10895213477792194736858887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14526951303722926315811849 10895213477792194736858887)
  ·
    refine ⟨16342820216688292105288331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10895213477792194736858887 16342820216688292105288331)
    ·
      refine ⟨24514230325032438157932497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16342820216688292105288331 24514230325032438157932497)
      ·
        refine ⟨18385672743774328618449373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24514230325032438157932497 18385672743774328618449373)
        ·
          refine ⟨6894627278915373231918515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18385672743774328618449373 6894627278915373231918515)
          ·
            refine ⟨10341940918373059847877773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6894627278915373231918515 10341940918373059847877773)
            ·
              refine ⟨3878227844389897442954165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10341940918373059847877773 3878227844389897442954165)
              ·
                refine ⟨363583860411552885276953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3878227844389897442954165 363583860411552885276953)
                ·
                  refine ⟨272687895308664663957715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 363583860411552885276953 272687895308664663957715)
                  ·
                    rfl

theorem cell20_597440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 5, 2].length) (baseStart_597440 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_597440 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_597440 prefixEnd_597440 := by exact prefixLift 597440
  have htrace : WordTrace (prefixWord ++ tailWord_597440) baseStart_597440 baseEnd_597440 := by
    simpa [prefixWord, tailWord_597440, baseEnd_597440] using wordTrace_append hprefix tailTrace_597440
  have hstable : (prefixWord ++ tailWord_597440).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597440).length < 2 ^ (prefixWord ++ tailWord_597440).sum := by decide
  have hdescent : baseEnd_597440 < baseStart_597440 := by decide
  rcases family_descends (prefixWord ++ tailWord_597440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597442 : List Nat := [3, 5, 2, 1, 2, 1, 1, 2, 3]
def baseStart_597442 : Nat := 118140960795 + 597442 * 2 ^ 59
def prefixEnd_597442 : Nat := 4983230072969 + 3 ^ 40 * 597442 * 2
def baseEnd_597442 : Nat := 272688808163161545891041

theorem tailTrace_597442 : CollatzResearch.WordTrace tailWord_597442 prefixEnd_597442 272688808163161545891041 := by
  unfold tailWord_597442
  simp only [CollatzResearch.WordTrace]
  refine ⟨5447624975394285953822645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14526999934384762543527053 5447624975394285953822645)
  ·
    refine ⟨510714841443214308170873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5447624975394285953822645 510714841443214308170873)
    ·
      refine ⟨383036131082410731128155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 510714841443214308170873 383036131082410731128155)
      ·
        refine ⟨574554196623616096692233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 383036131082410731128155 574554196623616096692233)
        ·
          refine ⟨430915647467712072519175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 574554196623616096692233 430915647467712072519175)
          ·
            refine ⟨646373471201568108778763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 430915647467712072519175 646373471201568108778763)
            ·
              refine ⟨969560206802352163168145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 646373471201568108778763 969560206802352163168145)
              ·
                refine ⟨727170155101764122376109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 969560206802352163168145 727170155101764122376109)
                ·
                  refine ⟨272688808163161545891041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 727170155101764122376109 272688808163161545891041)
                  ·
                    rfl

theorem cell20_597442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_597442 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_597442 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_597442 prefixEnd_597442 := by exact prefixLift 597442
  have htrace : WordTrace (prefixWord ++ tailWord_597442) baseStart_597442 baseEnd_597442 := by
    simpa [prefixWord, tailWord_597442, baseEnd_597442] using wordTrace_append hprefix tailTrace_597442
  have hstable : (prefixWord ++ tailWord_597442).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597442).length < 2 ^ (prefixWord ++ tailWord_597442).sum := by decide
  have hdescent : baseEnd_597442 < baseStart_597442 := by decide
  rcases family_descends (prefixWord ++ tailWord_597442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597471 : List Nat := [1, 1, 2, 3, 3, 1, 5, 1, 3]
def baseStart_597471 : Nat := 118140960795 + 597471 * 2 ^ 59
def prefixEnd_597471 : Nat := 4983230072969 + 3 ^ 40 * 597471 * 2
def baseEnd_597471 : Nat := 272702044553366333924255

theorem tailTrace_597471 : CollatzResearch.WordTrace tailWord_597471 prefixEnd_597471 272702044553366333924255 := by
  unfold tailWord_597471
  simp only [CollatzResearch.WordTrace]
  refine ⟨21791557618472081768096267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14527705078981387845397511 21791557618472081768096267)
  ·
    refine ⟨32687336427708122652144401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21791557618472081768096267 32687336427708122652144401)
    ·
      refine ⟨24515502320781091989108301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32687336427708122652144401 24515502320781091989108301)
      ·
        refine ⟨9193313370292909495915613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24515502320781091989108301 9193313370292909495915613)
        ·
          refine ⟨3447492513859841060968355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9193313370292909495915613 3447492513859841060968355)
          ·
            refine ⟨5171238770789761591452533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3447492513859841060968355 5171238770789761591452533)
            ·
              refine ⟨484803634761540149198675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5171238770789761591452533 484803634761540149198675)
              ·
                refine ⟨727205452142310223798013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 484803634761540149198675 727205452142310223798013)
                ·
                  refine ⟨272702044553366333924255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 727205452142310223798013 272702044553366333924255)
                  ·
                    rfl

theorem cell20_597471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 5, 1, 3].length) (baseStart_597471 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_597471 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_597471 prefixEnd_597471 := by exact prefixLift 597471
  have htrace : WordTrace (prefixWord ++ tailWord_597471) baseStart_597471 baseEnd_597471 := by
    simpa [prefixWord, tailWord_597471, baseEnd_597471] using wordTrace_append hprefix tailTrace_597471
  have hstable : (prefixWord ++ tailWord_597471).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597471).length < 2 ^ (prefixWord ++ tailWord_597471).sum := by decide
  have hdescent : baseEnd_597471 < baseStart_597471 := by decide
  rcases family_descends (prefixWord ++ tailWord_597471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597513 : List Nat := [1, 2, 1, 1, 3, 1, 3, 3, 5]
def baseStart_597513 : Nat := 118140960795 + 597513 * 2 ^ 59
def prefixEnd_597513 : Nat := 4983230072969 + 3 ^ 40 * 597513 * 2
def baseEnd_597513 : Nat := 272721214497800854524083

theorem tailTrace_597513 : CollatzResearch.WordTrace tailWord_597513 prefixEnd_597513 272721214497800854524083 := by
  unfold tailWord_597513
  simp only [CollatzResearch.WordTrace]
  refine ⟨21793089484319922941125193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14528726322879948627416795 21793089484319922941125193)
  ·
    refine ⟨16344817113239942205843895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21793089484319922941125193 16344817113239942205843895)
    ·
      refine ⟨24517225669859913308765843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16344817113239942205843895 24517225669859913308765843)
      ·
        refine ⟨36775838504789869963148765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24517225669859913308765843 36775838504789869963148765)
        ·
          refine ⟨13790939439296201236180787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36775838504789869963148765 13790939439296201236180787)
          ·
            refine ⟨20686409158944301854271181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13790939439296201236180787 20686409158944301854271181)
            ·
              refine ⟨7757403434604113195351693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20686409158944301854271181 7757403434604113195351693)
              ·
                refine ⟨2909026287976542448256885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7757403434604113195351693 2909026287976542448256885)
                ·
                  refine ⟨272721214497800854524083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2909026287976542448256885 272721214497800854524083)
                  ·
                    rfl

theorem cell20_597513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 5].length) (baseStart_597513 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_597513 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_597513 prefixEnd_597513 := by exact prefixLift 597513
  have htrace : WordTrace (prefixWord ++ tailWord_597513) baseStart_597513 baseEnd_597513 := by
    simpa [prefixWord, tailWord_597513, baseEnd_597513] using wordTrace_append hprefix tailTrace_597513
  have hstable : (prefixWord ++ tailWord_597513).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597513).length < 2 ^ (prefixWord ++ tailWord_597513).sum := by decide
  have hdescent : baseEnd_597513 < baseStart_597513 := by decide
  rcases family_descends (prefixWord ++ tailWord_597513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597554 : List Nat := [3, 2, 1, 1, 2, 1, 1, 7, 2]
def baseStart_597554 : Nat := 118140960795 + 597554 * 2 ^ 59
def prefixEnd_597554 : Nat := 4983230072969 + 3 ^ 40 * 597554 * 2
def baseEnd_597554 : Nat := 272739928014986934157249

theorem tailTrace_597554 : CollatzResearch.WordTrace tailWord_597554 prefixEnd_597554 272739928014986934157249 := by
  unfold tailWord_597554
  simp only [CollatzResearch.WordTrace]
  refine ⟨5448646219292846735841929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14529723251447591295578477 5448646219292846735841929)
  ·
    refine ⟨4086484664469635051881447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5448646219292846735841929 4086484664469635051881447)
    ·
      refine ⟨6129726996704452577822171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4086484664469635051881447 6129726996704452577822171)
      ·
        refine ⟨9194590495056678866733257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6129726996704452577822171 9194590495056678866733257)
        ·
          refine ⟨6895942871292509150049943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9194590495056678866733257 6895942871292509150049943)
          ·
            refine ⟨10343914306938763725074915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6895942871292509150049943 10343914306938763725074915)
            ·
              refine ⟨15515871460408145587612373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10343914306938763725074915 15515871460408145587612373)
              ·
                refine ⟨363653237353315912209665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 15515871460408145587612373 363653237353315912209665)
                ·
                  refine ⟨272739928014986934157249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 363653237353315912209665 272739928014986934157249)
                  ·
                    rfl

theorem cell20_597554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 7, 2].length) (baseStart_597554 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_597554 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_597554 prefixEnd_597554 := by exact prefixLift 597554
  have htrace : WordTrace (prefixWord ++ tailWord_597554) baseStart_597554 baseEnd_597554 := by
    simpa [prefixWord, tailWord_597554, baseEnd_597554] using wordTrace_append hprefix tailTrace_597554
  have hstable : (prefixWord ++ tailWord_597554).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597554).length < 2 ^ (prefixWord ++ tailWord_597554).sum := by decide
  have hdescent : baseEnd_597554 < baseStart_597554 := by decide
  rcases family_descends (prefixWord ++ tailWord_597554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597574 : List Nat := [6, 1, 1, 1, 4, 1, 1, 5]
def baseStart_597574 : Nat := 118140960795 + 597574 * 2 ^ 59
def prefixEnd_597574 : Nat := 4983230072969 + 3 ^ 40 * 597574 * 2
def baseEnd_597574 : Nat := 90916352186651917830167

theorem tailTrace_597574 : CollatzResearch.WordTrace tailWord_597574 prefixEnd_597574 90916352186651917830167 := by
  unfold tailWord_597574
  simp only [CollatzResearch.WordTrace]
  refine ⟨681103573034341573721743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14530209558065953572730517 681103573034341573721743)
  ·
    refine ⟨1021655359551512360582615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 681103573034341573721743 1021655359551512360582615)
    ·
      refine ⟨1532483039327268540873923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1021655359551512360582615 1532483039327268540873923)
      ·
        refine ⟨2298724558990902811310885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1532483039327268540873923 2298724558990902811310885)
        ·
          refine ⟨431010854810794277120791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2298724558990902811310885 431010854810794277120791)
          ·
            refine ⟨646516282216191415681187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 431010854810794277120791 646516282216191415681187)
            ·
              refine ⟨969774423324287123521781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 646516282216191415681187 969774423324287123521781)
              ·
                refine ⟨90916352186651917830167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 969774423324287123521781 90916352186651917830167)
                ·
                  rfl

theorem cell20_597574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_597574 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_597574 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_597574 prefixEnd_597574 := by exact prefixLift 597574
  have htrace : WordTrace (prefixWord ++ tailWord_597574) baseStart_597574 baseEnd_597574 := by
    simpa [prefixWord, tailWord_597574, baseEnd_597574] using wordTrace_append hprefix tailTrace_597574
  have hstable : (prefixWord ++ tailWord_597574).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597574).length < 2 ^ (prefixWord ++ tailWord_597574).sum := by decide
  have hdescent : baseEnd_597574 < baseStart_597574 := by decide
  rcases family_descends (prefixWord ++ tailWord_597574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597589 : List Nat := [1, 3, 2, 2, 1, 1, 1, 2, 7]
def baseStart_597589 : Nat := 118140960795 + 597589 * 2 ^ 59
def prefixEnd_597589 : Nat := 4983230072969 + 3 ^ 40 * 597589 * 2
def baseEnd_597589 : Nat := 272755902968682367990439

theorem tailTrace_597589 : CollatzResearch.WordTrace tailWord_597589 prefixEnd_597589 272755902968682367990439 := by
  unfold tailWord_597589
  simp only [CollatzResearch.WordTrace]
  refine ⟨21795861432044587920891821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14530574288029725280594547 21795861432044587920891821)
  ·
    refine ⟨8173448037016720470334433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21795861432044587920891821 8173448037016720470334433)
    ·
      refine ⟨6130086027762540352750825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8173448037016720470334433 6130086027762540352750825)
      ·
        refine ⟨4597564520821905264563119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6130086027762540352750825 4597564520821905264563119)
        ·
          refine ⟨6896346781232857896844679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4597564520821905264563119 6896346781232857896844679)
          ·
            refine ⟨10344520171849286845267019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6896346781232857896844679 10344520171849286845267019)
            ·
              refine ⟨15516780257773930267900529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10344520171849286845267019 15516780257773930267900529)
              ·
                refine ⟨11637585193330447700925397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15516780257773930267900529 11637585193330447700925397)
                ·
                  refine ⟨272755902968682367990439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11637585193330447700925397 272755902968682367990439)
                  ·
                    rfl

theorem cell20_597589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_597589 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_597589 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_597589 prefixEnd_597589 := by exact prefixLift 597589
  have htrace : WordTrace (prefixWord ++ tailWord_597589) baseStart_597589 baseEnd_597589 := by
    simpa [prefixWord, tailWord_597589, baseEnd_597589] using wordTrace_append hprefix tailTrace_597589
  have hstable : (prefixWord ++ tailWord_597589).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597589).length < 2 ^ (prefixWord ++ tailWord_597589).sum := by decide
  have hdescent : baseEnd_597589 < baseStart_597589 := by decide
  rcases family_descends (prefixWord ++ tailWord_597589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597627 : List Nat := [1, 1, 1, 1, 1, 4, 5, 1, 5]
def baseStart_597627 : Nat := 118140960795 + 597627 * 2 ^ 59
def prefixEnd_597627 : Nat := 4983230072969 + 3 ^ 40 * 597627 * 2
def baseEnd_597627 : Nat := 272773247204123124723617

theorem tailTrace_597627 : CollatzResearch.WordTrace tailWord_597627 prefixEnd_597627 272773247204123124723617 := by
  unfold tailWord_597627
  simp only [CollatzResearch.WordTrace]
  refine ⟨21797247405906920410775135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14531498270604613607183423 21797247405906920410775135)
  ·
    refine ⟨32695871108860380616162703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21797247405906920410775135 32695871108860380616162703)
    ·
      refine ⟨49043806663290570924244055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32695871108860380616162703 49043806663290570924244055)
      ·
        refine ⟨73565709994935856386366083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49043806663290570924244055 73565709994935856386366083)
        ·
          refine ⟨110348564992403784579549125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73565709994935856386366083 110348564992403784579549125)
          ·
            refine ⟨20690355936075709608665461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 110348564992403784579549125 20690355936075709608665461)
            ·
              refine ⟨1939720869007097775812387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20690355936075709608665461 1939720869007097775812387)
              ·
                refine ⟨2909581303510646663718581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1939720869007097775812387 2909581303510646663718581)
                ·
                  refine ⟨272773247204123124723617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2909581303510646663718581 272773247204123124723617)
                  ·
                    rfl

theorem cell20_597627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 5].length) (baseStart_597627 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_597627 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_597627 prefixEnd_597627 := by exact prefixLift 597627
  have htrace : WordTrace (prefixWord ++ tailWord_597627) baseStart_597627 baseEnd_597627 := by
    simpa [prefixWord, tailWord_597627, baseEnd_597627] using wordTrace_append hprefix tailTrace_597627
  have hstable : (prefixWord ++ tailWord_597627).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597627).length < 2 ^ (prefixWord ++ tailWord_597627).sum := by decide
  have hdescent : baseEnd_597627 < baseStart_597627 := by decide
  rcases family_descends (prefixWord ++ tailWord_597627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597685 : List Nat := [1, 3, 3, 3, 2, 2, 1, 1, 4]
def baseStart_597685 : Nat := 118140960795 + 597685 * 2 ^ 59
def prefixEnd_597685 : Nat := 4983230072969 + 3 ^ 40 * 597685 * 2
def baseEnd_597685 : Nat := 272799719984532700790047

theorem tailTrace_597685 : CollatzResearch.WordTrace tailWord_597685 prefixEnd_597685 272799719984532700790047 := by
  unfold tailWord_597685
  simp only [CollatzResearch.WordTrace]
  refine ⟨21799362839696796316386509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14532908559797864210924339 21799362839696796316386509)
  ·
    refine ⟨8174761064886298618644941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21799362839696796316386509 8174761064886298618644941)
    ·
      refine ⟨3065535399332361981991853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8174761064886298618644941 3065535399332361981991853)
      ·
        refine ⟨1149575774749635743246945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3065535399332361981991853 1149575774749635743246945)
        ·
          refine ⟨862181831062226807435209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1149575774749635743246945 862181831062226807435209)
          ·
            refine ⟨646636373296670105576407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 862181831062226807435209 646636373296670105576407)
            ·
              refine ⟨969954559945005158364611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 646636373296670105576407 969954559945005158364611)
              ·
                refine ⟨1454931839917507737546917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 969954559945005158364611 1454931839917507737546917)
                ·
                  refine ⟨272799719984532700790047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1454931839917507737546917 272799719984532700790047)
                  ·
                    rfl

theorem cell20_597685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 1, 4].length) (baseStart_597685 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_597685 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_597685 prefixEnd_597685 := by exact prefixLift 597685
  have htrace : WordTrace (prefixWord ++ tailWord_597685) baseStart_597685 baseEnd_597685 := by
    simpa [prefixWord, tailWord_597685, baseEnd_597685] using wordTrace_append hprefix tailTrace_597685
  have hstable : (prefixWord ++ tailWord_597685).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597685).length < 2 ^ (prefixWord ++ tailWord_597685).sum := by decide
  have hdescent : baseEnd_597685 < baseStart_597685 := by decide
  rcases family_descends (prefixWord ++ tailWord_597685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597689 : List Nat := [1, 2, 1, 4, 1, 1, 5, 1, 4]
def baseStart_597689 : Nat := 118140960795 + 597689 * 2 ^ 59
def prefixEnd_597689 : Nat := 4983230072969 + 3 ^ 40 * 597689 * 2
def baseEnd_597689 : Nat := 272801545693526464656697

theorem tailTrace_597689 : CollatzResearch.WordTrace tailWord_597689 prefixEnd_597689 272801545693526464656697 := by
  unfold tailWord_597689
  simp only [CollatzResearch.WordTrace]
  refine ⟨21799508731682304999532121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14533005821121536666354747 21799508731682304999532121)
  ·
    refine ⟨16349631548761728749649091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21799508731682304999532121 16349631548761728749649091)
    ·
      refine ⟨24524447323142593124473637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16349631548761728749649091 24524447323142593124473637)
      ·
        refine ⟨4598333873089236210838807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24524447323142593124473637 4598333873089236210838807)
        ·
          refine ⟨6897500809633854316258211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4598333873089236210838807 6897500809633854316258211)
          ·
            refine ⟨10346251214450781474387317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6897500809633854316258211 10346251214450781474387317)
            ·
              refine ⟨969961051354760763223811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10346251214450781474387317 969961051354760763223811)
              ·
                refine ⟨1454941577032141144835717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 969961051354760763223811 1454941577032141144835717)
                ·
                  refine ⟨272801545693526464656697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1454941577032141144835717 272801545693526464656697)
                  ·
                    rfl

theorem cell20_597689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 1, 4].length) (baseStart_597689 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_597689 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_597689 prefixEnd_597689 := by exact prefixLift 597689
  have htrace : WordTrace (prefixWord ++ tailWord_597689) baseStart_597689 baseEnd_597689 := by
    simpa [prefixWord, tailWord_597689, baseEnd_597689] using wordTrace_append hprefix tailTrace_597689
  have hstable : (prefixWord ++ tailWord_597689).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597689).length < 2 ^ (prefixWord ++ tailWord_597689).sum := by decide
  have hdescent : baseEnd_597689 < baseStart_597689 := by decide
  rcases family_descends (prefixWord ++ tailWord_597689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597696 : List Nat := [2, 1, 1, 2, 4, 1, 4, 5]
def baseStart_597696 : Nat := 118140960795 + 597696 * 2 ^ 59
def prefixEnd_597696 : Nat := 4983230072969 + 3 ^ 40 * 597696 * 2
def baseEnd_597696 : Nat := 90934913561421850474445

theorem tailTrace_597696 : CollatzResearch.WordTrace tailWord_597696 prefixEnd_597696 90934913561421850474445 := by
  unfold tailWord_597696
  simp only [CollatzResearch.WordTrace]
  refine ⟨10899882021328472597518471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14533176028437963463357961 10899882021328472597518471)
  ·
    refine ⟨16349823031992708896277707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10899882021328472597518471 16349823031992708896277707)
    ·
      refine ⟨24524734547989063344416561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16349823031992708896277707 24524734547989063344416561)
      ·
        refine ⟨18393550910991797508312421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24524734547989063344416561 18393550910991797508312421)
        ·
          refine ⟨3448790795810962032808579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18393550910991797508312421 3448790795810962032808579)
          ·
            refine ⟨5173186193716443049212869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3448790795810962032808579 5173186193716443049212869)
            ·
              refine ⟨969972411321833071727413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5173186193716443049212869 969972411321833071727413)
              ·
                refine ⟨90934913561421850474445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 969972411321833071727413 90934913561421850474445)
                ·
                  rfl

theorem cell20_597696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 5].length) (baseStart_597696 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_597696 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_597696 prefixEnd_597696 := by exact prefixLift 597696
  have htrace : WordTrace (prefixWord ++ tailWord_597696) baseStart_597696 baseEnd_597696 := by
    simpa [prefixWord, tailWord_597696, baseEnd_597696] using wordTrace_append hprefix tailTrace_597696
  have hstable : (prefixWord ++ tailWord_597696).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597696).length < 2 ^ (prefixWord ++ tailWord_597696).sum := by decide
  have hdescent : baseEnd_597696 < baseStart_597696 := by decide
  rcases family_descends (prefixWord ++ tailWord_597696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597755 : List Nat := [1, 1, 1, 1, 1, 3, 1, 11]
def baseStart_597755 : Nat := 118140960795 + 597755 * 2 ^ 59
def prefixEnd_597755 : Nat := 4983230072969 + 3 ^ 40 * 597755 * 2
def baseEnd_597755 : Nat := 90943889963974522818809

theorem tailTrace_597755 : CollatzResearch.WordTrace tailWord_597755 prefixEnd_597755 90943889963974522818809 := by
  unfold tailWord_597755
  simp only [CollatzResearch.WordTrace]
  refine ⟨21801915949443198271434719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14534610632962132180956479 21801915949443198271434719)
  ·
    refine ⟨32702873924164797407152079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21801915949443198271434719 32702873924164797407152079)
    ·
      refine ⟨49054310886247196110728119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32702873924164797407152079 49054310886247196110728119)
      ·
        refine ⟨73581466329370794166092179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49054310886247196110728119 73581466329370794166092179)
        ·
          refine ⟨110372199494056191249138269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73581466329370794166092179 110372199494056191249138269)
          ·
            refine ⟨41389574810271071718426851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110372199494056191249138269 41389574810271071718426851)
            ·
              refine ⟨62084362215406607577640277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41389574810271071718426851 62084362215406607577640277)
              ·
                refine ⟨90943889963974522818809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 62084362215406607577640277 90943889963974522818809)
                ·
                  rfl

theorem cell20_597755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 11].length) (baseStart_597755 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_597755 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_597755 prefixEnd_597755 := by exact prefixLift 597755
  have htrace : WordTrace (prefixWord ++ tailWord_597755) baseStart_597755 baseEnd_597755 := by
    simpa [prefixWord, tailWord_597755, baseEnd_597755] using wordTrace_append hprefix tailTrace_597755
  have hstable : (prefixWord ++ tailWord_597755).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597755).length < 2 ^ (prefixWord ++ tailWord_597755).sum := by decide
  have hdescent : baseEnd_597755 < baseStart_597755 := by decide
  rcases family_descends (prefixWord ++ tailWord_597755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597778 : List Nat := [3, 2, 4, 1, 1, 2, 2, 3, 2]
def baseStart_597778 : Nat := 118140960795 + 597778 * 2 ^ 59
def prefixEnd_597778 : Nat := 4983230072969 + 3 ^ 40 * 597778 * 2
def baseEnd_597778 : Nat := 272842167718637710689667

theorem tailTrace_597778 : CollatzResearch.WordTrace tailWord_597778 prefixEnd_597778 272842167718637710689667 := by
  unfold tailWord_597778
  simp only [CollatzResearch.WordTrace]
  refine ⟨5450688707089968299880497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14535169885573248799681325 5450688707089968299880497)
  ·
    refine ⟨4088016530317476224910373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5450688707089968299880497 4088016530317476224910373)
    ·
      refine ⟨766503099434526792170695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4088016530317476224910373 766503099434526792170695)
      ·
        refine ⟨1149754649151790188256043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 766503099434526792170695 1149754649151790188256043)
        ·
          refine ⟨1724631973727685282384065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1149754649151790188256043 1724631973727685282384065)
          ·
            refine ⟨1293473980295763961788049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1724631973727685282384065 1293473980295763961788049)
            ·
              refine ⟨970105485221822971341037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1293473980295763961788049 970105485221822971341037)
              ·
                refine ⟨363789556958183614252889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 970105485221822971341037 363789556958183614252889)
                ·
                  refine ⟨272842167718637710689667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 363789556958183614252889 272842167718637710689667)
                  ·
                    rfl

theorem cell20_597778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 3, 2].length) (baseStart_597778 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_597778 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_597778 prefixEnd_597778 := by exact prefixLift 597778
  have htrace : WordTrace (prefixWord ++ tailWord_597778) baseStart_597778 baseEnd_597778 := by
    simpa [prefixWord, tailWord_597778, baseEnd_597778] using wordTrace_append hprefix tailTrace_597778
  have hstable : (prefixWord ++ tailWord_597778).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597778).length < 2 ^ (prefixWord ++ tailWord_597778).sum := by decide
  have hdescent : baseEnd_597778 < baseStart_597778 := by decide
  rcases family_descends (prefixWord ++ tailWord_597778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597796 : List Nat := [2, 3, 1, 3, 2, 2, 1, 1, 5]
def baseStart_597796 : Nat := 118140960795 + 597796 * 2 ^ 59
def prefixEnd_597796 : Nat := 4983230072969 + 3 ^ 40 * 597796 * 2
def baseEnd_597796 : Nat := 272850383409109648089593

theorem tailTrace_597796 : CollatzResearch.WordTrace tailWord_597796 prefixEnd_597796 272850383409109648089593 := by
  unfold tailWord_597796
  simp only [CollatzResearch.WordTrace]
  refine ⟨10901705671147331136838621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14535607561529774849118161 10901705671147331136838621)
  ·
    refine ⟨4088139626680249176314483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10901705671147331136838621 4088139626680249176314483)
    ·
      refine ⟨6132209440020373764471725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4088139626680249176314483 6132209440020373764471725)
      ·
        refine ⟨2299578540007640161676897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6132209440020373764471725 2299578540007640161676897)
        ·
          refine ⟨1724683905005730121257673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2299578540007640161676897 1724683905005730121257673)
          ·
            refine ⟨1293512928754297590943255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1724683905005730121257673 1293512928754297590943255)
            ·
              refine ⟨1940269393131446386414883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1293512928754297590943255 1940269393131446386414883)
              ·
                refine ⟨2910404089697169579622325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1940269393131446386414883 2910404089697169579622325)
                ·
                  refine ⟨272850383409109648089593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2910404089697169579622325 272850383409109648089593)
                  ·
                    rfl

theorem cell20_597796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_597796 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_597796 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_597796 prefixEnd_597796 := by exact prefixLift 597796
  have htrace : WordTrace (prefixWord ++ tailWord_597796) baseStart_597796 baseEnd_597796 := by
    simpa [prefixWord, tailWord_597796, baseEnd_597796] using wordTrace_append hprefix tailTrace_597796
  have hstable : (prefixWord ++ tailWord_597796).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597796).length < 2 ^ (prefixWord ++ tailWord_597796).sum := by decide
  have hdescent : baseEnd_597796 < baseStart_597796 := by decide
  rcases family_descends (prefixWord ++ tailWord_597796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597827 : List Nat := [1, 1, 1, 3, 1, 7, 2, 4]
def baseStart_597827 : Nat := 118140960795 + 597827 * 2 ^ 59
def prefixEnd_597827 : Nat := 4983230072969 + 3 ^ 40 * 597827 * 2
def baseEnd_597827 : Nat := 90954844217937106018711

theorem tailTrace_597827 : CollatzResearch.WordTrace tailWord_597827 prefixEnd_597827 90954844217937106018711 := by
  unfold tailWord_597827
  simp only [CollatzResearch.WordTrace]
  refine ⟨21804542005182354568055735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14536361336788236378703823 21804542005182354568055735)
  ·
    refine ⟨32706813007773531852083603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21804542005182354568055735 32706813007773531852083603)
    ·
      refine ⟨49060219511660297778125405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32706813007773531852083603 49060219511660297778125405)
      ·
        refine ⟨18397582316872611666797027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49060219511660297778125405 18397582316872611666797027)
        ·
          refine ⟨27596373475308917500195541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18397582316872611666797027 27596373475308917500195541)
          ·
            refine ⟨646790003327552753910833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 27596373475308917500195541 646790003327552753910833)
            ·
              refine ⟨485092502495664565433125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 646790003327552753910833 485092502495664565433125)
              ·
                refine ⟨90954844217937106018711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 485092502495664565433125 90954844217937106018711)
                ·
                  rfl

theorem cell20_597827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 2, 4].length) (baseStart_597827 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_597827 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_597827 prefixEnd_597827 := by exact prefixLift 597827
  have htrace : WordTrace (prefixWord ++ tailWord_597827) baseStart_597827 baseEnd_597827 := by
    simpa [prefixWord, tailWord_597827, baseEnd_597827] using wordTrace_append hprefix tailTrace_597827
  have hstable : (prefixWord ++ tailWord_597827).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597827).length < 2 ^ (prefixWord ++ tailWord_597827).sum := by decide
  have hdescent : baseEnd_597827 < baseStart_597827 := by decide
  rcases family_descends (prefixWord ++ tailWord_597827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597855 : List Nat := [1, 1, 2, 3, 1, 4, 2, 1, 5]
def baseStart_597855 : Nat := 118140960795 + 597855 * 2 ^ 59
def prefixEnd_597855 : Nat := 4983230072969 + 3 ^ 40 * 597855 * 2
def baseEnd_597855 : Nat := 272877312616767665122685

theorem tailTrace_597855 : CollatzResearch.WordTrace tailWord_597855 prefixEnd_597855 272877312616767665122685 := by
  unfold tailWord_597855
  simp only [CollatzResearch.WordTrace]
  refine ⟨21805563249080915350075019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14537042166053943566716679 21805563249080915350075019)
  ·
    refine ⟨32708344873621373025112529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21805563249080915350075019 32708344873621373025112529)
    ·
      refine ⟨24531258655216029768834397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32708344873621373025112529 24531258655216029768834397)
      ·
        refine ⟨9199221995706011163312899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24531258655216029768834397 9199221995706011163312899)
        ·
          refine ⟨13798832993559016744969349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9199221995706011163312899 13798832993559016744969349)
          ·
            refine ⟨2587281186292315639681753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13798832993559016744969349 2587281186292315639681753)
            ·
              refine ⟨1940460889719236729761315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2587281186292315639681753 1940460889719236729761315)
              ·
                refine ⟨2910691334578855094641973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1940460889719236729761315 2910691334578855094641973)
                ·
                  refine ⟨272877312616767665122685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2910691334578855094641973 272877312616767665122685)
                  ·
                    rfl

theorem cell20_597855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 5].length) (baseStart_597855 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_597855 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_597855 prefixEnd_597855 := by exact prefixLift 597855
  have htrace : WordTrace (prefixWord ++ tailWord_597855) baseStart_597855 baseEnd_597855 := by
    simpa [prefixWord, tailWord_597855, baseEnd_597855] using wordTrace_append hprefix tailTrace_597855
  have hstable : (prefixWord ++ tailWord_597855).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597855).length < 2 ^ (prefixWord ++ tailWord_597855).sum := by decide
  have hdescent : baseEnd_597855 < baseStart_597855 := by decide
  rcases family_descends (prefixWord ++ tailWord_597855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597858 : List Nat := [3, 3, 2, 1, 2, 1, 3, 1, 4]
def baseStart_597858 : Nat := 118140960795 + 597858 * 2 ^ 59
def prefixEnd_597858 : Nat := 4983230072969 + 3 ^ 40 * 597858 * 2
def baseEnd_597858 : Nat := 272878681898512988022673

theorem tailTrace_597858 : CollatzResearch.WordTrace tailWord_597858 prefixEnd_597858 272878681898512988022673 := by
  unfold tailWord_597858
  simp only [CollatzResearch.WordTrace]
  refine ⟨5451418167017511715608557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14537115112046697908289485 5451418167017511715608557)
  ·
    refine ⟨2044281812631566893353209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5451418167017511715608557 2044281812631566893353209)
    ·
      refine ⟨1533211359473675170014907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2044281812631566893353209 1533211359473675170014907)
      ·
        refine ⟨2299817039210512755022361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1533211359473675170014907 2299817039210512755022361)
        ·
          refine ⟨1724862779407884566266771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2299817039210512755022361 1724862779407884566266771)
          ·
            refine ⟨2587294169111826849400157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1724862779407884566266771 2587294169111826849400157)
            ·
              refine ⟨970235313416935068525059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2587294169111826849400157 970235313416935068525059)
              ·
                refine ⟨1455352970125402602787589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 970235313416935068525059 1455352970125402602787589)
                ·
                  refine ⟨272878681898512988022673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1455352970125402602787589 272878681898512988022673)
                  ·
                    rfl

theorem cell20_597858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_597858 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_597858 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_597858 prefixEnd_597858 := by exact prefixLift 597858
  have htrace : WordTrace (prefixWord ++ tailWord_597858) baseStart_597858 baseEnd_597858 := by
    simpa [prefixWord, tailWord_597858, baseEnd_597858] using wordTrace_append hprefix tailTrace_597858
  have hstable : (prefixWord ++ tailWord_597858).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597858).length < 2 ^ (prefixWord ++ tailWord_597858).sum := by decide
  have hdescent : baseEnd_597858 < baseStart_597858 := by decide
  rcases family_descends (prefixWord ++ tailWord_597858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597924 : List Nat := [2, 3, 1, 2, 1, 3, 3, 5]
def baseStart_597924 : Nat := 118140960795 + 597924 * 2 ^ 59
def prefixEnd_597924 : Nat := 4983230072969 + 3 ^ 40 * 597924 * 2
def baseEnd_597924 : Nat := 90969602032303363940801

theorem tailTrace_597924 : CollatzResearch.WordTrace tailWord_597924 prefixEnd_597924 90969602032303363940801 := by
  unfold tailWord_597924
  simp only [CollatzResearch.WordTrace]
  refine ⟨10904039942915470067168413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14538719923887293422891217 10904039942915470067168413)
  ·
    refine ⟨4089014978593301275188155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10904039942915470067168413 4089014978593301275188155)
    ·
      refine ⟨6133522467889951912782233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4089014978593301275188155 6133522467889951912782233)
      ·
        refine ⟨4600141850917463934586675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6133522467889951912782233 4600141850917463934586675)
        ·
          refine ⟨6900212776376195901880013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4600141850917463934586675 6900212776376195901880013)
          ·
            refine ⟨2587579791141073463205005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6900212776376195901880013 2587579791141073463205005)
            ·
              refine ⟨970342421677902548701877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2587579791141073463205005 970342421677902548701877)
              ·
                refine ⟨90969602032303363940801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 970342421677902548701877 90969602032303363940801)
                ·
                  rfl

theorem cell20_597924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 5].length) (baseStart_597924 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_597924 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_597924 prefixEnd_597924 := by exact prefixLift 597924
  have htrace : WordTrace (prefixWord ++ tailWord_597924) baseStart_597924 baseEnd_597924 := by
    simpa [prefixWord, tailWord_597924, baseEnd_597924] using wordTrace_append hprefix tailTrace_597924
  have hstable : (prefixWord ++ tailWord_597924).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597924).length < 2 ^ (prefixWord ++ tailWord_597924).sum := by decide
  have hdescent : baseEnd_597924 < baseStart_597924 := by decide
  rcases family_descends (prefixWord ++ tailWord_597924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597941 : List Nat := [1, 3, 3, 2, 1, 3, 3, 4]
def baseStart_597941 : Nat := 118140960795 + 597941 * 2 ^ 59
def prefixEnd_597941 : Nat := 4983230072969 + 3 ^ 40 * 597941 * 2
def baseEnd_597941 : Nat := 90972188453377862751889

theorem tailTrace_597941 : CollatzResearch.WordTrace tailWord_597941 prefixEnd_597941 90972188453377862751889 := by
  unfold tailWord_597941
  simp only [CollatzResearch.WordTrace]
  refine ⟨21808699926769352037705677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14539133284512901358470451 21808699926769352037705677)
  ·
    refine ⟨8178262472538507014139629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21808699926769352037705677 8178262472538507014139629)
    ·
      refine ⟨3066848427201940130302361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8178262472538507014139629 3066848427201940130302361)
      ·
        refine ⟨2300136320401455097726771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3066848427201940130302361 2300136320401455097726771)
        ·
          refine ⟨3450204480602182646590157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2300136320401455097726771 3450204480602182646590157)
          ·
            refine ⟨1293826680225818492471309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3450204480602182646590157 1293826680225818492471309)
            ·
              refine ⟨485185005084681934676741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1293826680225818492471309 485185005084681934676741)
              ·
                refine ⟨90972188453377862751889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 485185005084681934676741 90972188453377862751889)
                ·
                  rfl

theorem cell20_597941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 3, 4].length) (baseStart_597941 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_597941 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_597941 prefixEnd_597941 := by exact prefixLift 597941
  have htrace : WordTrace (prefixWord ++ tailWord_597941) baseStart_597941 baseEnd_597941 := by
    simpa [prefixWord, tailWord_597941, baseEnd_597941] using wordTrace_append hprefix tailTrace_597941
  have hstable : (prefixWord ++ tailWord_597941).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597941).length < 2 ^ (prefixWord ++ tailWord_597941).sum := by decide
  have hdescent : baseEnd_597941 < baseStart_597941 := by decide
  rcases family_descends (prefixWord ++ tailWord_597941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597969 : List Nat := [1, 2, 2, 1, 2, 1, 2, 6, 3]
def baseStart_597969 : Nat := 118140960795 + 597969 * 2 ^ 59
def prefixEnd_597969 : Nat := 4983230072969 + 3 ^ 40 * 597969 * 2
def baseEnd_597969 : Nat := 272929345323089935322219

theorem tailTrace_597969 : CollatzResearch.WordTrace tailWord_597969 prefixEnd_597969 272929345323089935322219 := by
  unfold tailWord_597969
  simp only [CollatzResearch.WordTrace]
  refine ⟨21809721170667912819724961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14539814113778608546483307 21809721170667912819724961)
  ·
    refine ⟨16357290878000934614793721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21809721170667912819724961 16357290878000934614793721)
    ·
      refine ⟨12267968158500700961095291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16357290878000934614793721 12267968158500700961095291)
      ·
        refine ⟨18401952237751051441642937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12267968158500700961095291 18401952237751051441642937)
        ·
          refine ⟨13801464178313288581232203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18401952237751051441642937 13801464178313288581232203)
          ·
            refine ⟨20702196267469932871848305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13801464178313288581232203 20702196267469932871848305)
            ·
              refine ⟨15526647200602449653886229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20702196267469932871848305 15526647200602449653886229)
              ·
                refine ⟨727811587528239827525917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15526647200602449653886229 727811587528239827525917)
                ·
                  refine ⟨272929345323089935322219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 727811587528239827525917 272929345323089935322219)
                  ·
                    rfl

theorem cell20_597969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 6, 3].length) (baseStart_597969 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_597969 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_597969 prefixEnd_597969 := by exact prefixLift 597969
  have htrace : WordTrace (prefixWord ++ tailWord_597969) baseStart_597969 baseEnd_597969 := by
    simpa [prefixWord, tailWord_597969, baseEnd_597969] using wordTrace_append hprefix tailTrace_597969
  have hstable : (prefixWord ++ tailWord_597969).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597969).length < 2 ^ (prefixWord ++ tailWord_597969).sum := by decide
  have hdescent : baseEnd_597969 < baseStart_597969 := by decide
  rcases family_descends (prefixWord ++ tailWord_597969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597972 : List Nat := [2, 4, 1, 2, 1, 1, 1, 6, 2]
def baseStart_597972 : Nat := 118140960795 + 597972 * 2 ^ 59
def prefixEnd_597972 : Nat := 4983230072969 + 3 ^ 40 * 597972 * 2
def baseEnd_597972 : Nat := 272930714604835258222207

theorem tailTrace_597972 : CollatzResearch.WordTrace tailWord_597972 prefixEnd_597972 272930714604835258222207 := by
  unfold tailWord_597972
  simp only [CollatzResearch.WordTrace]
  refine ⟨10904915294828522166042085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14539887059771362888056113 10904915294828522166042085)
  ·
    refine ⟨2044671617780347906132891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10904915294828522166042085 2044671617780347906132891)
    ·
      refine ⟨3067007426670521859199337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2044671617780347906132891 3067007426670521859199337)
      ·
        refine ⟨2300255570002891394399503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3067007426670521859199337 2300255570002891394399503)
        ·
          refine ⟨3450383355004337091599255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2300255570002891394399503 3450383355004337091599255)
          ·
            refine ⟨5175575032506505637398883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3450383355004337091599255 5175575032506505637398883)
            ·
              refine ⟨7763362548759758456098325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5175575032506505637398883 7763362548759758456098325)
              ·
                refine ⟨363907619473113677629609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7763362548759758456098325 363907619473113677629609)
                ·
                  refine ⟨272930714604835258222207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 363907619473113677629609 272930714604835258222207)
                  ·
                    rfl

theorem cell20_597972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 6, 2].length) (baseStart_597972 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_597972 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_597972 prefixEnd_597972 := by exact prefixLift 597972
  have htrace : WordTrace (prefixWord ++ tailWord_597972) baseStart_597972 baseEnd_597972 := by
    simpa [prefixWord, tailWord_597972, baseEnd_597972] using wordTrace_append hprefix tailTrace_597972
  have hstable : (prefixWord ++ tailWord_597972).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597972).length < 2 ^ (prefixWord ++ tailWord_597972).sum := by decide
  have hdescent : baseEnd_597972 < baseStart_597972 := by decide
  rcases family_descends (prefixWord ++ tailWord_597972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598000 : List Nat := [2, 1, 1, 1, 3, 2, 6, 4]
def baseStart_598000 : Nat := 118140960795 + 598000 * 2 ^ 59
def prefixEnd_598000 : Nat := 4983230072969 + 3 ^ 40 * 598000 * 2
def baseEnd_598000 : Nat := 90981164855930535096253

theorem tailTrace_598000 : CollatzResearch.WordTrace tailWord_598000 prefixEnd_598000 90981164855930535096253 := by
  unfold tailWord_598000
  simp only [CollatzResearch.WordTrace]
  refine ⟨10905425916777802557051727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14540567889037070076068969 10905425916777802557051727)
  ·
    refine ⟨16358138875166703835577591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10905425916777802557051727 16358138875166703835577591)
    ·
      refine ⟨24537208312750055753366387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16358138875166703835577591 24537208312750055753366387)
      ·
        refine ⟨36805812469125083630049581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24537208312750055753366387 36805812469125083630049581)
        ·
          refine ⟨13802179675921906361268593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36805812469125083630049581 13802179675921906361268593)
          ·
            refine ⟨10351634756941429770951445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13802179675921906361268593 10351634756941429770951445)
            ·
              refine ⟨485232879231629520513349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10351634756941429770951445 485232879231629520513349)
              ·
                refine ⟨90981164855930535096253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 485232879231629520513349 90981164855930535096253)
                ·
                  rfl

theorem cell20_598000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 6, 4].length) (baseStart_598000 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_598000 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_598000 prefixEnd_598000 := by exact prefixLift 598000
  have htrace : WordTrace (prefixWord ++ tailWord_598000) baseStart_598000 baseEnd_598000 := by
    simpa [prefixWord, tailWord_598000, baseEnd_598000] using wordTrace_append hprefix tailTrace_598000
  have hstable : (prefixWord ++ tailWord_598000).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598000).length < 2 ^ (prefixWord ++ tailWord_598000).sum := by decide
  have hdescent : baseEnd_598000 < baseStart_598000 := by decide
  rcases family_descends (prefixWord ++ tailWord_598000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598006 : List Nat := [5, 1, 1, 1, 4, 2, 1, 3, 2]
def baseStart_598006 : Nat := 118140960795 + 598006 * 2 ^ 59
def prefixEnd_598006 : Nat := 4983230072969 + 3 ^ 40 * 598006 * 2
def baseEnd_598006 : Nat := 272946233131282251088735

theorem tailTrace_598006 : CollatzResearch.WordTrace tailWord_598006 prefixEnd_598006 272946233131282251088735 := by
  unfold tailWord_598006
  simp only [CollatzResearch.WordTrace]
  refine ⟨1363191916970866758676367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14540713781022578759214581 1363191916970866758676367)
  ·
    refine ⟨2044787875456300138014551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1363191916970866758676367 2044787875456300138014551)
    ·
      refine ⟨3067181813184450207021827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2044787875456300138014551 3067181813184450207021827)
      ·
        refine ⟨4600772719776675310532741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3067181813184450207021827 4600772719776675310532741)
        ·
          refine ⟨862644884958126620724889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4600772719776675310532741 862644884958126620724889)
          ·
            refine ⟨646983663718594965543667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 862644884958126620724889 646983663718594965543667)
            ·
              refine ⟨970475495577892448315501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 646983663718594965543667 970475495577892448315501)
              ·
                refine ⟨363928310841709668118313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 970475495577892448315501 363928310841709668118313)
                ·
                  refine ⟨272946233131282251088735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 363928310841709668118313 272946233131282251088735)
                  ·
                    rfl

theorem cell20_598006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 3, 2].length) (baseStart_598006 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_598006 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_598006 prefixEnd_598006 := by exact prefixLift 598006
  have htrace : WordTrace (prefixWord ++ tailWord_598006) baseStart_598006 baseEnd_598006 := by
    simpa [prefixWord, tailWord_598006, baseEnd_598006] using wordTrace_append hprefix tailTrace_598006
  have hstable : (prefixWord ++ tailWord_598006).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598006).length < 2 ^ (prefixWord ++ tailWord_598006).sum := by decide
  have hdescent : baseEnd_598006 < baseStart_598006 := by decide
  rcases family_descends (prefixWord ++ tailWord_598006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598021 : List Nat := [1, 3, 1, 1, 2, 4, 8]
def baseStart_598021 : Nat := 118140960795 + 598021 * 2 ^ 59
def prefixEnd_598021 : Nat := 4983230072969 + 3 ^ 40 * 598021 * 2
def baseEnd_598021 : Nat := 30328119948889873954297

theorem tailTrace_598021 : CollatzResearch.WordTrace tailWord_598021 prefixEnd_598021 30328119948889873954297 := by
  unfold tailWord_598021
  simp only [CollatzResearch.WordTrace]
  refine ⟨21811617766479525700617917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14541078510986350467078611 21811617766479525700617917)
  ·
    refine ⟨8179356662429822137731719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21811617766479525700617917 8179356662429822137731719)
    ·
      refine ⟨12269034993644733206597579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8179356662429822137731719 12269034993644733206597579)
      ·
        refine ⟨18403552490467099809896369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12269034993644733206597579 18403552490467099809896369)
        ·
          refine ⟨13802664367850324857422277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18403552490467099809896369 13802664367850324857422277)
          ·
            refine ⟨2587999568971935910766677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13802664367850324857422277 2587999568971935910766677)
            ·
              refine ⟨30328119948889873954297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2587999568971935910766677 30328119948889873954297)
              ·
                rfl

theorem cell20_598021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 8].length) (baseStart_598021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_598021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_598021 prefixEnd_598021 := by exact prefixLift 598021
  have htrace : WordTrace (prefixWord ++ tailWord_598021) baseStart_598021 baseEnd_598021 := by
    simpa [prefixWord, tailWord_598021, baseEnd_598021] using wordTrace_append hprefix tailTrace_598021
  have hstable : (prefixWord ++ tailWord_598021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598021).length < 2 ^ (prefixWord ++ tailWord_598021).sum := by decide
  have hdescent : baseEnd_598021 < baseStart_598021 := by decide
  rcases family_descends (prefixWord ++ tailWord_598021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598086 : List Nat := [6, 1, 1, 1, 1, 1, 2, 3, 4]
def baseStart_598086 : Nat := 118140960795 + 598086 * 2 ^ 59
def prefixEnd_598086 : Nat := 4983230072969 + 3 ^ 40 * 598086 * 2
def baseEnd_598086 : Nat := 272982747311157528421741

theorem tailTrace_598086 : CollatzResearch.WordTrace tailWord_598086 prefixEnd_598086 272982747311157528421741 := by
  unfold tailWord_598086
  simp only [CollatzResearch.WordTrace]
  refine ⟨681687140976376306304191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14542659007496027867822741 681687140976376306304191)
  ·
    refine ⟨1022530711464564459456287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 681687140976376306304191 1022530711464564459456287)
    ·
      refine ⟨1533796067196846689184431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1022530711464564459456287 1533796067196846689184431)
      ·
        refine ⟨2300694100795270033776647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1533796067196846689184431 2300694100795270033776647)
        ·
          refine ⟨3451041151192905050664971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2300694100795270033776647 3451041151192905050664971)
          ·
            refine ⟨5176561726789357575997457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3451041151192905050664971 5176561726789357575997457)
            ·
              refine ⟨3882421295092018181998093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5176561726789357575997457 3882421295092018181998093)
              ·
                refine ⟨1455907985659506818249285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3882421295092018181998093 1455907985659506818249285)
                ·
                  refine ⟨272982747311157528421741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1455907985659506818249285 272982747311157528421741)
                  ·
                    rfl

theorem cell20_598086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_598086 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_598086 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_598086 prefixEnd_598086 := by exact prefixLift 598086
  have htrace : WordTrace (prefixWord ++ tailWord_598086) baseStart_598086 baseEnd_598086 := by
    simpa [prefixWord, tailWord_598086, baseEnd_598086] using wordTrace_append hprefix tailTrace_598086
  have hstable : (prefixWord ++ tailWord_598086).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598086).length < 2 ^ (prefixWord ++ tailWord_598086).sum := by decide
  have hdescent : baseEnd_598086 < baseStart_598086 := by decide
  rcases family_descends (prefixWord ++ tailWord_598086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598090 : List Nat := [3, 1, 2, 1, 1, 2, 1, 5, 4]
def baseStart_598090 : Nat := 118140960795 + 598090 * 2 ^ 59
def prefixEnd_598090 : Nat := 4983230072969 + 3 ^ 40 * 598090 * 2
def baseEnd_598090 : Nat := 272984573020151292288391

theorem tailTrace_598090 : CollatzResearch.WordTrace tailWord_598090 prefixEnd_598090 272984573020151292288391 := by
  unfold tailWord_598090
  simp only [CollatzResearch.WordTrace]
  refine ⟨5453533600807387621219931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14542756268819700323253149 5453533600807387621219931)
  ·
    refine ⟨8180300401211081431829897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5453533600807387621219931 8180300401211081431829897)
    ·
      refine ⟨6135225300908311073872423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8180300401211081431829897 6135225300908311073872423)
      ·
        refine ⟨9202837951362466610808635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6135225300908311073872423 9202837951362466610808635)
        ·
          refine ⟨13804256927043699916212953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9202837951362466610808635 13804256927043699916212953)
          ·
            refine ⟨10353192695282774937159715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13804256927043699916212953 10353192695282774937159715)
            ·
              refine ⟨15529789042924162405739573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10353192695282774937159715 15529789042924162405739573)
              ·
                refine ⟨1455917722774140225538085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15529789042924162405739573 1455917722774140225538085)
                ·
                  refine ⟨272984573020151292288391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1455917722774140225538085 272984573020151292288391)
                  ·
                    rfl

theorem cell20_598090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 5, 4].length) (baseStart_598090 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_598090 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_598090 prefixEnd_598090 := by exact prefixLift 598090
  have htrace : WordTrace (prefixWord ++ tailWord_598090) baseStart_598090 baseEnd_598090 := by
    simpa [prefixWord, tailWord_598090, baseEnd_598090] using wordTrace_append hprefix tailTrace_598090
  have hstable : (prefixWord ++ tailWord_598090).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598090).length < 2 ^ (prefixWord ++ tailWord_598090).sum := by decide
  have hdescent : baseEnd_598090 < baseStart_598090 := by decide
  rcases family_descends (prefixWord ++ tailWord_598090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598124 : List Nat := [2, 2, 1, 1, 3, 4, 2, 3, 2]
def baseStart_598124 : Nat := 118140960795 + 598124 * 2 ^ 59
def prefixEnd_598124 : Nat := 4983230072969 + 3 ^ 40 * 598124 * 2
def baseEnd_598124 : Nat := 273000091546598285154919

theorem tailTrace_598124 : CollatzResearch.WordTrace tailWord_598124 prefixEnd_598124 273000091546598285154919 := by
  unfold tailWord_598124
  simp only [CollatzResearch.WordTrace]
  refine ⟨10907687242553187145808713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14543582990070916194411617 10907687242553187145808713)
  ·
    refine ⟨8180765431914890359356535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10907687242553187145808713 8180765431914890359356535)
    ·
      refine ⟨12271148147872335539034803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8180765431914890359356535 12271148147872335539034803)
      ·
        refine ⟨18406722221808503308552205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12271148147872335539034803 18406722221808503308552205)
        ·
          refine ⟨6902520833178188740707077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18406722221808503308552205 6902520833178188740707077)
          ·
            refine ⟨1294222656220910388882577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6902520833178188740707077 1294222656220910388882577)
            ·
              refine ⟨970666992165682791661933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1294222656220910388882577 970666992165682791661933)
              ·
                refine ⟨364000122062131046873225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 970666992165682791661933 364000122062131046873225)
                ·
                  refine ⟨273000091546598285154919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 364000122062131046873225 273000091546598285154919)
                  ·
                    rfl

theorem cell20_598124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 3, 2].length) (baseStart_598124 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_598124 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_598124 prefixEnd_598124 := by exact prefixLift 598124
  have htrace : WordTrace (prefixWord ++ tailWord_598124) baseStart_598124 baseEnd_598124 := by
    simpa [prefixWord, tailWord_598124, baseEnd_598124] using wordTrace_append hprefix tailTrace_598124
  have hstable : (prefixWord ++ tailWord_598124).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598124).length < 2 ^ (prefixWord ++ tailWord_598124).sum := by decide
  have hdescent : baseEnd_598124 < baseStart_598124 := by decide
  rcases family_descends (prefixWord ++ tailWord_598124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598135 : List Nat := [1, 1, 3, 1, 1, 6, 7]
def baseStart_598135 : Nat := 118140960795 + 598135 * 2 ^ 59
def prefixEnd_598135 : Nat := 4983230072969 + 3 ^ 40 * 598135 * 2
def baseEnd_598135 : Nat := 30333901360703459532023

theorem tailTrace_598135 : CollatzResearch.WordTrace tailWord_598135 prefixEnd_598135 30333901360703459532023 := by
  unfold tailWord_598135
  simp only [CollatzResearch.WordTrace]
  refine ⟨21815775688066523170267859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14543850458711015446845239 21815775688066523170267859)
  ·
    refine ⟨32723663532099784755401789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21815775688066523170267859 32723663532099784755401789)
    ·
      refine ⟨12271373824537419283275671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32723663532099784755401789 12271373824537419283275671)
      ·
        refine ⟨18407060736806128924913507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12271373824537419283275671 18407060736806128924913507)
        ·
          refine ⟨27610591105209193387370261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18407060736806128924913507 27610591105209193387370261)
          ·
            refine ⟨1294246458056680940032981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 27610591105209193387370261 1294246458056680940032981)
            ·
              refine ⟨30333901360703459532023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1294246458056680940032981 30333901360703459532023)
              ·
                rfl

theorem cell20_598135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 7].length) (baseStart_598135 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_598135 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_598135 prefixEnd_598135 := by exact prefixLift 598135
  have htrace : WordTrace (prefixWord ++ tailWord_598135) baseStart_598135 baseEnd_598135 := by
    simpa [prefixWord, tailWord_598135, baseEnd_598135] using wordTrace_append hprefix tailTrace_598135
  have hstable : (prefixWord ++ tailWord_598135).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598135).length < 2 ^ (prefixWord ++ tailWord_598135).sum := by decide
  have hdescent : baseEnd_598135 < baseStart_598135 := by decide
  rcases family_descends (prefixWord ++ tailWord_598135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598186 : List Nat := [3, 1, 5, 1, 3, 1, 6]
def baseStart_598186 : Nat := 118140960795 + 598186 * 2 ^ 59
def prefixEnd_598186 : Nat := 4983230072969 + 3 ^ 40 * 598186 * 2
def baseEnd_598186 : Nat := 30336487781777958343111

theorem tailTrace_598186 : CollatzResearch.WordTrace tailWord_598186 prefixEnd_598186 30336487781777958343111 := by
  unfold tailWord_598186
  simp only [CollatzResearch.WordTrace]
  refine ⟨5454408952720439720093603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14545090540587839253582941 5454408952720439720093603)
  ·
    refine ⟨8181613429080659580140405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5454408952720439720093603 8181613429080659580140405)
    ·
      refine ⟨767026258976311835638163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8181613429080659580140405 767026258976311835638163)
      ·
        refine ⟨1150539388464467753457245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 767026258976311835638163 1150539388464467753457245)
        ·
          refine ⟨431452270674175407546467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1150539388464467753457245 431452270674175407546467)
          ·
            refine ⟨647178406011263111319701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 431452270674175407546467 647178406011263111319701)
            ·
              refine ⟨30336487781777958343111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 647178406011263111319701 30336487781777958343111)
              ·
                rfl

theorem cell20_598186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 6].length) (baseStart_598186 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_598186 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_598186 prefixEnd_598186 := by exact prefixLift 598186
  have htrace : WordTrace (prefixWord ++ tailWord_598186) baseStart_598186 baseEnd_598186 := by
    simpa [prefixWord, tailWord_598186, baseEnd_598186] using wordTrace_append hprefix tailTrace_598186
  have hstable : (prefixWord ++ tailWord_598186).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598186).length < 2 ^ (prefixWord ++ tailWord_598186).sum := by decide
  have hdescent : baseEnd_598186 < baseStart_598186 := by decide
  rcases family_descends (prefixWord ++ tailWord_598186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598200 : List Nat := [2, 1, 2, 1, 2, 1, 7, 2, 2]
def baseStart_598200 : Nat := 118140960795 + 598200 * 2 ^ 59
def prefixEnd_598200 : Nat := 4983230072969 + 3 ^ 40 * 598200 * 2
def baseEnd_598200 : Nat := 273034780017479798621275

theorem tailTrace_598200 : CollatzResearch.WordTrace tailWord_598200 prefixEnd_598200 273034780017479798621275 := by
  unfold tailWord_598200
  simp only [CollatzResearch.WordTrace]
  refine ⟨10909073216415519635692027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14545430955220692847589369 10909073216415519635692027)
  ·
    refine ⟨16363609824623279453538041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10909073216415519635692027 16363609824623279453538041)
    ·
      refine ⟨12272707368467459590153531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16363609824623279453538041 12272707368467459590153531)
      ·
        refine ⟨18409061052701189385230297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12272707368467459590153531 18409061052701189385230297)
        ·
          refine ⟨13806795789525892038922723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18409061052701189385230297 13806795789525892038922723)
          ·
            refine ⟨20710193684288838058384085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13806795789525892038922723 20710193684288838058384085)
            ·
              refine ⟨485395164475519641993377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 20710193684288838058384085 485395164475519641993377)
              ·
                refine ⟨364046373356639731495033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 485395164475519641993377 364046373356639731495033)
                ·
                  refine ⟨273034780017479798621275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 364046373356639731495033 273034780017479798621275)
                  ·
                    rfl

theorem cell20_598200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 7, 2, 2].length) (baseStart_598200 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_598200 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_598200 prefixEnd_598200 := by exact prefixLift 598200
  have htrace : WordTrace (prefixWord ++ tailWord_598200) baseStart_598200 baseEnd_598200 := by
    simpa [prefixWord, tailWord_598200, baseEnd_598200] using wordTrace_append hprefix tailTrace_598200
  have hstable : (prefixWord ++ tailWord_598200).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598200).length < 2 ^ (prefixWord ++ tailWord_598200).sum := by decide
  have hdescent : baseEnd_598200 < baseStart_598200 := by decide
  rcases family_descends (prefixWord ++ tailWord_598200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598210 : List Nat := [3, 5, 1, 1, 1, 2, 1, 3, 3]
def baseStart_598210 : Nat := 118140960795 + 598210 * 2 ^ 59
def prefixEnd_598210 : Nat := 4983230072969 + 3 ^ 40 * 598210 * 2
def baseEnd_598210 : Nat := 273039344289964208287901

theorem tailTrace_598210 : CollatzResearch.WordTrace tailWord_598210 prefixEnd_598210 273039344289964208287901 := by
  unfold tailWord_598210
  simp only [CollatzResearch.WordTrace]
  refine ⟨5454627790698702744812021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14545674108529873986165389 5454627790698702744812021)
  ·
    refine ⟨511371355378003382326127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5454627790698702744812021 511371355378003382326127)
    ·
      refine ⟨767057033067005073489191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 511371355378003382326127 767057033067005073489191)
      ·
        refine ⟨1150585549600507610233787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 767057033067005073489191 1150585549600507610233787)
        ·
          refine ⟨1725878324400761415350681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1150585549600507610233787 1725878324400761415350681)
          ·
            refine ⟨1294408743300571061513011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1725878324400761415350681 1294408743300571061513011)
            ·
              refine ⟨1941613114950856592269517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1294408743300571061513011 1941613114950856592269517)
              ·
                refine ⟨728104918106571222101069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1941613114950856592269517 728104918106571222101069)
                ·
                  refine ⟨273039344289964208287901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 728104918106571222101069 273039344289964208287901)
                  ·
                    rfl

theorem cell20_598210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_598210 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_598210 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_598210 prefixEnd_598210 := by exact prefixLift 598210
  have htrace : WordTrace (prefixWord ++ tailWord_598210) baseStart_598210 baseEnd_598210 := by
    simpa [prefixWord, tailWord_598210, baseEnd_598210] using wordTrace_append hprefix tailTrace_598210
  have hstable : (prefixWord ++ tailWord_598210).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598210).length < 2 ^ (prefixWord ++ tailWord_598210).sum := by decide
  have hdescent : baseEnd_598210 < baseStart_598210 := by decide
  rcases family_descends (prefixWord ++ tailWord_598210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598255 : List Nat := [1, 1, 2, 1, 6, 3, 2, 2, 2]
def baseStart_598255 : Nat := 118140960795 + 598255 * 2 ^ 59
def prefixEnd_598255 : Nat := 4983230072969 + 3 ^ 40 * 598255 * 2
def baseEnd_598255 : Nat := 273059883516144051787717

theorem tailTrace_598255 : CollatzResearch.WordTrace tailWord_598255 prefixEnd_598255 273059883516144051787717 := by
  unfold tailWord_598255
  simp only [CollatzResearch.WordTrace]
  refine ⟨21820152447631783664636219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14546768298421189109757479 21820152447631783664636219)
  ·
    refine ⟨32730228671447675496954329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21820152447631783664636219 32730228671447675496954329)
    ·
      refine ⟨24547671503585756622715747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32730228671447675496954329 24547671503585756622715747)
      ·
        refine ⟨36821507255378634934073621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24547671503585756622715747 36821507255378634934073621)
        ·
          refine ⟨1726008152595873512534701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 36821507255378634934073621 1726008152595873512534701)
          ·
            refine ⟨647253057223452567200513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1726008152595873512534701 647253057223452567200513)
            ·
              refine ⟨485439792917589425400385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 647253057223452567200513 485439792917589425400385)
              ·
                refine ⟨364079844688192069050289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 485439792917589425400385 364079844688192069050289)
                ·
                  refine ⟨273059883516144051787717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 364079844688192069050289 273059883516144051787717)
                  ·
                    rfl

theorem cell20_598255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 2, 2, 2].length) (baseStart_598255 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_598255 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_598255 prefixEnd_598255 := by exact prefixLift 598255
  have htrace : WordTrace (prefixWord ++ tailWord_598255) baseStart_598255 baseEnd_598255 := by
    simpa [prefixWord, tailWord_598255, baseEnd_598255] using wordTrace_append hprefix tailTrace_598255
  have hstable : (prefixWord ++ tailWord_598255).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598255).length < 2 ^ (prefixWord ++ tailWord_598255).sum := by decide
  have hdescent : baseEnd_598255 < baseStart_598255 := by decide
  rcases family_descends (prefixWord ++ tailWord_598255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598256 : List Nat := [2, 1, 1, 1, 3, 1, 1, 5, 5]
def baseStart_598256 : Nat := 118140960795 + 598256 * 2 ^ 59
def prefixEnd_598256 : Nat := 4983230072969 + 3 ^ 40 * 598256 * 2
def baseEnd_598256 : Nat := 273060339943392492754379

theorem tailTrace_598256 : CollatzResearch.WordTrace tailWord_598256 prefixEnd_598256 273060339943392492754379 := by
  unfold tailWord_598256
  simp only [CollatzResearch.WordTrace]
  refine ⟨10910094460314080417711311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14546792613752107223615081 10910094460314080417711311)
  ·
    refine ⟨16365141690471120626566967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10910094460314080417711311 16365141690471120626566967)
    ·
      refine ⟨24547712535706680939850451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16365141690471120626566967 24547712535706680939850451)
      ·
        refine ⟨36821568803560021409775677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24547712535706680939850451 36821568803560021409775677)
        ·
          refine ⟨13808088301335008028665879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36821568803560021409775677 13808088301335008028665879)
          ·
            refine ⟨20712132452002512042998819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13808088301335008028665879 20712132452002512042998819)
            ·
              refine ⟨31068198678003768064498229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20712132452002512042998819 31068198678003768064498229)
              ·
                refine ⟨2912643626062853256046709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31068198678003768064498229 2912643626062853256046709)
                ·
                  refine ⟨273060339943392492754379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2912643626062853256046709 273060339943392492754379)
                  ·
                    rfl

theorem cell20_598256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 5].length) (baseStart_598256 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_598256 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_598256 prefixEnd_598256 := by exact prefixLift 598256
  have htrace : WordTrace (prefixWord ++ tailWord_598256) baseStart_598256 baseEnd_598256 := by
    simpa [prefixWord, tailWord_598256, baseEnd_598256] using wordTrace_append hprefix tailTrace_598256
  have hstable : (prefixWord ++ tailWord_598256).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598256).length < 2 ^ (prefixWord ++ tailWord_598256).sum := by decide
  have hdescent : baseEnd_598256 < baseStart_598256 := by decide
  rcases family_descends (prefixWord ++ tailWord_598256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598259 : List Nat := [1, 1, 1, 2, 2, 4, 3, 4, 2]
def baseStart_598259 : Nat := 118140960795 + 598259 * 2 ^ 59
def prefixEnd_598259 : Nat := 4983230072969 + 3 ^ 40 * 598259 * 2
def baseEnd_598259 : Nat := 273061709225137815654367

theorem tailTrace_598259 : CollatzResearch.WordTrace tailWord_598259 prefixEnd_598259 273061709225137815654367 := by
  unfold tailWord_598259
  simp only [CollatzResearch.WordTrace]
  refine ⟨21820298339617292347781831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14546865559744861565187887 21820298339617292347781831)
  ·
    refine ⟨32730447509425938521672747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21820298339617292347781831 32730447509425938521672747)
    ·
      refine ⟨49095671264138907782509121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32730447509425938521672747 49095671264138907782509121)
      ·
        refine ⟨36821753448104180836881841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49095671264138907782509121 36821753448104180836881841)
        ·
          refine ⟨27616315086078135627661381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36821753448104180836881841 27616315086078135627661381)
          ·
            refine ⟨5178059078639650430186509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27616315086078135627661381 5178059078639650430186509)
            ·
              refine ⟨1941772154489868911319941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5178059078639650430186509 1941772154489868911319941)
              ·
                refine ⟨364082278966850420872489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1941772154489868911319941 364082278966850420872489)
                ·
                  refine ⟨273061709225137815654367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 364082278966850420872489 273061709225137815654367)
                  ·
                    rfl

theorem cell20_598259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 4, 2].length) (baseStart_598259 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_598259 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_598259 prefixEnd_598259 := by exact prefixLift 598259
  have htrace : WordTrace (prefixWord ++ tailWord_598259) baseStart_598259 baseEnd_598259 := by
    simpa [prefixWord, tailWord_598259, baseEnd_598259] using wordTrace_append hprefix tailTrace_598259
  have hstable : (prefixWord ++ tailWord_598259).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598259).length < 2 ^ (prefixWord ++ tailWord_598259).sum := by decide
  have hdescent : baseEnd_598259 < baseStart_598259 := by decide
  rcases family_descends (prefixWord ++ tailWord_598259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598266 : List Nat := [3, 1, 1, 1, 1, 7, 1, 5]
def baseStart_598266 : Nat := 118140960795 + 598266 * 2 ^ 59
def prefixEnd_598266 : Nat := 4983230072969 + 3 ^ 40 * 598266 * 2
def baseEnd_598266 : Nat := 91021634738625634140335

theorem tailTrace_598266 : CollatzResearch.WordTrace tailWord_598266 prefixEnd_598266 91021634738625634140335 := by
  unfold tailWord_598266
  simp only [CollatzResearch.WordTrace]
  refine ⟨5455138412647983135821663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14547035767061288362191101 5455138412647983135821663)
  ·
    refine ⟨8182707618971974703732495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5455138412647983135821663 8182707618971974703732495)
    ·
      refine ⟨12274061428457962055598743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8182707618971974703732495 12274061428457962055598743)
      ·
        refine ⟨18411092142686943083398115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12274061428457962055598743 18411092142686943083398115)
        ·
          refine ⟨27616638214030414625097173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18411092142686943083398115 27616638214030414625097173)
          ·
            refine ⟨647264958141337842775715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 27616638214030414625097173 647264958141337842775715)
            ·
              refine ⟨970897437212006764163573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 647264958141337842775715 970897437212006764163573)
              ·
                refine ⟨91021634738625634140335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 970897437212006764163573 91021634738625634140335)
                ·
                  rfl

theorem cell20_598266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 5].length) (baseStart_598266 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_598266 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_598266 prefixEnd_598266 := by exact prefixLift 598266
  have htrace : WordTrace (prefixWord ++ tailWord_598266) baseStart_598266 baseEnd_598266 := by
    simpa [prefixWord, tailWord_598266, baseEnd_598266] using wordTrace_append hprefix tailTrace_598266
  have hstable : (prefixWord ++ tailWord_598266).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598266).length < 2 ^ (prefixWord ++ tailWord_598266).sum := by decide
  have hdescent : baseEnd_598266 < baseStart_598266 := by decide
  rcases family_descends (prefixWord ++ tailWord_598266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598273 : List Nat := [1, 2, 4, 1, 1, 2, 1, 5, 3]
def baseStart_598273 : Nat := 118140960795 + 598273 * 2 ^ 59
def prefixEnd_598273 : Nat := 4983230072969 + 3 ^ 40 * 598273 * 2
def baseEnd_598273 : Nat := 273068099206615989187643

theorem tailTrace_598273 : CollatzResearch.WordTrace tailWord_598273 prefixEnd_598273 273068099206615989187643 := by
  unfold tailWord_598273
  simp only [CollatzResearch.WordTrace]
  refine ⟨21820808961566572738791473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14547205974377715159194315 21820808961566572738791473)
  ·
    refine ⟨16365606721174929554093605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21820808961566572738791473 16365606721174929554093605)
    ·
      refine ⟨3068551260220299291392551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16365606721174929554093605 3068551260220299291392551)
      ·
        refine ⟨4602826890330448937088827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3068551260220299291392551 4602826890330448937088827)
        ·
          refine ⟨6904240335495673405633241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4602826890330448937088827 6904240335495673405633241)
          ·
            refine ⟨5178180251621755054224931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6904240335495673405633241 5178180251621755054224931)
            ·
              refine ⟨7767270377432632581337397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5178180251621755054224931 7767270377432632581337397)
              ·
                refine ⟨728181597884309304500381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7767270377432632581337397 728181597884309304500381)
                ·
                  refine ⟨273068099206615989187643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 728181597884309304500381 273068099206615989187643)
                  ·
                    rfl

theorem cell20_598273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 5, 3].length) (baseStart_598273 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_598273 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_598273 prefixEnd_598273 := by exact prefixLift 598273
  have htrace : WordTrace (prefixWord ++ tailWord_598273) baseStart_598273 baseEnd_598273 := by
    simpa [prefixWord, tailWord_598273, baseEnd_598273] using wordTrace_append hprefix tailTrace_598273
  have hstable : (prefixWord ++ tailWord_598273).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598273).length < 2 ^ (prefixWord ++ tailWord_598273).sum := by decide
  have hdescent : baseEnd_598273 < baseStart_598273 := by decide
  rcases family_descends (prefixWord ++ tailWord_598273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598280 : List Nat := [2, 1, 3, 2, 3, 1, 1, 1, 6]
def baseStart_598280 : Nat := 118140960795 + 598280 * 2 ^ 59
def prefixEnd_598280 : Nat := 4983230072969 + 3 ^ 40 * 598280 * 2
def baseEnd_598280 : Nat := 273071294197355075954281

theorem tailTrace_598280 : CollatzResearch.WordTrace tailWord_598280 prefixEnd_598280 273071294197355075954281 := by
  unfold tailWord_598280
  simp only [CollatzResearch.WordTrace]
  refine ⟨10910532136270606467148147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14547376181694141956197529 10910532136270606467148147)
  ·
    refine ⟨16365798204405909700722221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10910532136270606467148147 16365798204405909700722221)
    ·
      refine ⟨6137174326652216137770833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16365798204405909700722221 6137174326652216137770833)
      ·
        refine ⟨4602880744989162103328125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6137174326652216137770833 4602880744989162103328125)
        ·
          refine ⟨1726080279370935788748047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4602880744989162103328125 1726080279370935788748047)
          ·
            refine ⟨2589120419056403683122071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1726080279370935788748047 2589120419056403683122071)
            ·
              refine ⟨3883680628584605524683107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2589120419056403683122071 3883680628584605524683107)
              ·
                refine ⟨5825520942876908287024661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3883680628584605524683107 5825520942876908287024661)
                ·
                  refine ⟨273071294197355075954281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5825520942876908287024661 273071294197355075954281)
                  ·
                    rfl

theorem cell20_598280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 6].length) (baseStart_598280 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_598280 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_598280 prefixEnd_598280 := by exact prefixLift 598280
  have htrace : WordTrace (prefixWord ++ tailWord_598280) baseStart_598280 baseEnd_598280 := by
    simpa [prefixWord, tailWord_598280, baseEnd_598280] using wordTrace_append hprefix tailTrace_598280
  have hstable : (prefixWord ++ tailWord_598280).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598280).length < 2 ^ (prefixWord ++ tailWord_598280).sum := by decide
  have hdescent : baseEnd_598280 < baseStart_598280 := by decide
  rcases family_descends (prefixWord ++ tailWord_598280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598314 : List Nat := [3, 1, 4, 2, 2, 1, 2, 1, 4]
def baseStart_598314 : Nat := 118140960795 + 598314 * 2 ^ 59
def prefixEnd_598314 : Nat := 4983230072969 + 3 ^ 40 * 598314 * 2
def baseEnd_598314 : Nat := 273086812723802068820809

theorem tailTrace_598314 : CollatzResearch.WordTrace tailWord_598314 prefixEnd_598314 273086812723802068820809 := by
  unfold tailWord_598314
  simp only [CollatzResearch.WordTrace]
  refine ⟨5455576088604509185258499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14548202902945357827355997 5455576088604509185258499)
  ·
    refine ⟨8183364132906763777887749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5455576088604509185258499 8183364132906763777887749)
    ·
      refine ⟨1534380774920018208353953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8183364132906763777887749 1534380774920018208353953)
      ·
        refine ⟨1150785581190013656265465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1534380774920018208353953 1150785581190013656265465)
        ·
          refine ⟨863089185892510242199099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1150785581190013656265465 863089185892510242199099)
          ·
            refine ⟨1294633778838765363298649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 863089185892510242199099 1294633778838765363298649)
            ·
              refine ⟨970975334129074022473987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1294633778838765363298649 970975334129074022473987)
              ·
                refine ⟨1456463001193611033710981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 970975334129074022473987 1456463001193611033710981)
                ·
                  refine ⟨273086812723802068820809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1456463001193611033710981 273086812723802068820809)
                  ·
                    rfl

theorem cell20_598314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 1, 4].length) (baseStart_598314 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_598314 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_598314 prefixEnd_598314 := by exact prefixLift 598314
  have htrace : WordTrace (prefixWord ++ tailWord_598314) baseStart_598314 baseEnd_598314 := by
    simpa [prefixWord, tailWord_598314, baseEnd_598314] using wordTrace_append hprefix tailTrace_598314
  have hstable : (prefixWord ++ tailWord_598314).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598314).length < 2 ^ (prefixWord ++ tailWord_598314).sum := by decide
  have hdescent : baseEnd_598314 < baseStart_598314 := by decide
  rcases family_descends (prefixWord ++ tailWord_598314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598325 : List Nat := [1, 3, 3, 1, 2, 1, 2, 7]
def baseStart_598325 : Nat := 118140960795 + 598325 * 2 ^ 59
def prefixEnd_598325 : Nat := 4983230072969 + 3 ^ 40 * 598325 * 2
def baseEnd_598325 : Nat := 91030611141178306484699

theorem tailTrace_598325 : CollatzResearch.WordTrace tailWord_598325 prefixEnd_598325 91030611141178306484699 := by
  unfold tailWord_598325
  simp only [CollatzResearch.WordTrace]
  refine ⟨21822705557378185619684429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14548470371585457079789619 21822705557378185619684429)
  ·
    refine ⟨8183514584016819607381661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21822705557378185619684429 8183514584016819607381661)
    ·
      refine ⟨3068817969006307352768123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8183514584016819607381661 3068817969006307352768123)
      ·
        refine ⟨4603226953509461029152185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3068817969006307352768123 4603226953509461029152185)
        ·
          refine ⟨3452420215132095771864139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4603226953509461029152185 3452420215132095771864139)
          ·
            refine ⟨5178630322698143657796209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3452420215132095771864139 5178630322698143657796209)
            ·
              refine ⟨3883972742023607743347157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5178630322698143657796209 3883972742023607743347157)
              ·
                refine ⟨91030611141178306484699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3883972742023607743347157 91030611141178306484699)
                ·
                  rfl

theorem cell20_598325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 7].length) (baseStart_598325 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_598325 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_598325 prefixEnd_598325 := by exact prefixLift 598325
  have htrace : WordTrace (prefixWord ++ tailWord_598325) baseStart_598325 baseEnd_598325 := by
    simpa [prefixWord, tailWord_598325, baseEnd_598325] using wordTrace_append hprefix tailTrace_598325
  have hstable : (prefixWord ++ tailWord_598325).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598325).length < 2 ^ (prefixWord ++ tailWord_598325).sum := by decide
  have hdescent : baseEnd_598325 < baseStart_598325 := by decide
  rcases family_descends (prefixWord ++ tailWord_598325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598352 : List Nat := [2, 1, 1, 1, 1, 8, 1, 3, 2]
def baseStart_598352 : Nat := 118140960795 + 598352 * 2 ^ 59
def prefixEnd_598352 : Nat := 4983230072969 + 3 ^ 40 * 598352 * 2
def baseEnd_598352 : Nat := 273104156959242825553987

theorem tailTrace_598352 : CollatzResearch.WordTrace tailWord_598352 prefixEnd_598352 273104156959242825553987 := by
  unfold tailWord_598352
  simp only [CollatzResearch.WordTrace]
  refine ⟨10911845164140184615458655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14549126885520246153944873 10911845164140184615458655)
  ·
    refine ⟨16367767746210276923187983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10911845164140184615458655 16367767746210276923187983)
    ·
      refine ⟨24551651619315415384781975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16367767746210276923187983 24551651619315415384781975)
      ·
        refine ⟨36827477428973123077172963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24551651619315415384781975 36827477428973123077172963)
        ·
          refine ⟨55241216143459684615759445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36827477428973123077172963 55241216143459684615759445)
          ·
            refine ⟨647358001681168179090931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 55241216143459684615759445 647358001681168179090931)
            ·
              refine ⟨971037002521752268636397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 647358001681168179090931 971037002521752268636397)
              ·
                refine ⟨364138875945657100738649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 971037002521752268636397 364138875945657100738649)
                ·
                  refine ⟨273104156959242825553987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 364138875945657100738649 273104156959242825553987)
                  ·
                    rfl

theorem cell20_598352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 3, 2].length) (baseStart_598352 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_598352 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_598352 prefixEnd_598352 := by exact prefixLift 598352
  have htrace : WordTrace (prefixWord ++ tailWord_598352) baseStart_598352 baseEnd_598352 := by
    simpa [prefixWord, tailWord_598352, baseEnd_598352] using wordTrace_append hprefix tailTrace_598352
  have hstable : (prefixWord ++ tailWord_598352).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598352).length < 2 ^ (prefixWord ++ tailWord_598352).sum := by decide
  have hdescent : baseEnd_598352 < baseStart_598352 := by decide
  rcases family_descends (prefixWord ++ tailWord_598352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598373 : List Nat := [1, 3, 1, 3, 1, 5, 1, 1, 4]
def baseStart_598373 : Nat := 118140960795 + 598373 * 2 ^ 59
def prefixEnd_598373 : Nat := 4983230072969 + 3 ^ 40 * 598373 * 2
def baseEnd_598373 : Nat := 273113741931460085853901

theorem tailTrace_598373 : CollatzResearch.WordTrace tailWord_598373 prefixEnd_598373 273113741931460085853901 := by
  unfold tailWord_598373
  simp only [CollatzResearch.WordTrace]
  refine ⟨21824456261204289817431773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14549637507469526544954515 21824456261204289817431773)
  ·
    refine ⟨8184171097951608681536915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21824456261204289817431773 8184171097951608681536915)
    ·
      refine ⟨12276256646927413022305373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8184171097951608681536915 12276256646927413022305373)
      ·
        refine ⟨4603596242597779883364515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12276256646927413022305373 4603596242597779883364515)
        ·
          refine ⟨6905394363896669825046773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4603596242597779883364515 6905394363896669825046773)
          ·
            refine ⟨647380721615312796098135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6905394363896669825046773 647380721615312796098135)
            ·
              refine ⟨971071082422969194147203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 647380721615312796098135 971071082422969194147203)
              ·
                refine ⟨1456606623634453791220805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 971071082422969194147203 1456606623634453791220805)
                ·
                  refine ⟨273113741931460085853901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1456606623634453791220805 273113741931460085853901)
                  ·
                    rfl

theorem cell20_598373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 1, 4].length) (baseStart_598373 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_598373 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_598373 prefixEnd_598373 := by exact prefixLift 598373
  have htrace : WordTrace (prefixWord ++ tailWord_598373) baseStart_598373 baseEnd_598373 := by
    simpa [prefixWord, tailWord_598373, baseEnd_598373] using wordTrace_append hprefix tailTrace_598373
  have hstable : (prefixWord ++ tailWord_598373).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598373).length < 2 ^ (prefixWord ++ tailWord_598373).sum := by decide
  have hdescent : baseEnd_598373 < baseStart_598373 := by decide
  rcases family_descends (prefixWord ++ tailWord_598373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598380 : List Nat := [2, 2, 1, 1, 6, 1, 2, 5]
def baseStart_598380 : Nat := 118140960795 + 598380 * 2 ^ 59
def prefixEnd_598380 : Nat := 4983230072969 + 3 ^ 40 * 598380 * 2
def baseEnd_598380 : Nat := 91038978974066390873513

theorem tailTrace_598380 : CollatzResearch.WordTrace tailWord_598380 prefixEnd_598380 91038978974066390873513 := by
  unfold tailWord_598380
  simp only [CollatzResearch.WordTrace]
  refine ⟨10912355786089465006468297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14549807714785953341957729 10912355786089465006468297)
  ·
    refine ⟨8184266839567098754851223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10912355786089465006468297 8184266839567098754851223)
    ·
      refine ⟨12276400259350648132276835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8184266839567098754851223 12276400259350648132276835)
      ·
        refine ⟨18414600389025972198415253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12276400259350648132276835 18414600389025972198415253)
        ·
          refine ⟨863184393235592446800715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 18414600389025972198415253 863184393235592446800715)
          ·
            refine ⟨1294776589853388670201073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 863184393235592446800715 1294776589853388670201073)
            ·
              refine ⟨971082442390041502650805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1294776589853388670201073 971082442390041502650805)
              ·
                refine ⟨91038978974066390873513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 971082442390041502650805 91038978974066390873513)
                ·
                  rfl

theorem cell20_598380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 5].length) (baseStart_598380 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_598380 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_598380 prefixEnd_598380 := by exact prefixLift 598380
  have htrace : WordTrace (prefixWord ++ tailWord_598380) baseStart_598380 baseEnd_598380 := by
    simpa [prefixWord, tailWord_598380, baseEnd_598380] using wordTrace_append hprefix tailTrace_598380
  have hstable : (prefixWord ++ tailWord_598380).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598380).length < 2 ^ (prefixWord ++ tailWord_598380).sum := by decide
  have hdescent : baseEnd_598380 < baseStart_598380 := by decide
  rcases family_descends (prefixWord ++ tailWord_598380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598425 : List Nat := [1, 2, 1, 2, 1, 4, 4, 2, 3]
def baseStart_598425 : Nat := 118140960795 + 598425 * 2 ^ 59
def prefixEnd_598425 : Nat := 4983230072969 + 3 ^ 40 * 598425 * 2
def baseEnd_598425 : Nat := 273137476148379016120355

theorem tailTrace_598425 : CollatzResearch.WordTrace tailWord_598425 prefixEnd_598425 273137476148379016120355 := by
  unfold tailWord_598425
  simp only [CollatzResearch.WordTrace]
  refine ⟨21826352857015902698324729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14550901904677268465549819 21826352857015902698324729)
  ·
    refine ⟨16369764642761927023743547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21826352857015902698324729 16369764642761927023743547)
    ·
      refine ⟨24554646964142890535615321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16369764642761927023743547 24554646964142890535615321)
      ·
        refine ⟨18415985223107167901711491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24554646964142890535615321 18415985223107167901711491)
        ·
          refine ⟨27623977834660751852567237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18415985223107167901711491 27623977834660751852567237)
          ·
            refine ⟨5179495843998890972356357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27623977834660751852567237 5179495843998890972356357)
            ·
              refine ⟨971155470749792057316817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5179495843998890972356357 971155470749792057316817)
              ·
                refine ⟨728366603062344042987613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 971155470749792057316817 728366603062344042987613)
                ·
                  refine ⟨273137476148379016120355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 728366603062344042987613 273137476148379016120355)
                  ·
                    rfl

theorem cell20_598425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 2, 3].length) (baseStart_598425 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_598425 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_598425 prefixEnd_598425 := by exact prefixLift 598425
  have htrace : WordTrace (prefixWord ++ tailWord_598425) baseStart_598425 baseEnd_598425 := by
    simpa [prefixWord, tailWord_598425, baseEnd_598425] using wordTrace_append hprefix tailTrace_598425
  have hstable : (prefixWord ++ tailWord_598425).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598425).length < 2 ^ (prefixWord ++ tailWord_598425).sum := by decide
  have hdescent : baseEnd_598425 < baseStart_598425 := by decide
  rcases family_descends (prefixWord ++ tailWord_598425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598532 : List Nat := [2, 3, 2, 3, 1, 3, 6]
def baseStart_598532 : Nat := 118140960795 + 598532 * 2 ^ 59
def prefixEnd_598532 : Nat := 4983230072969 + 3 ^ 40 * 598532 * 2
def baseEnd_598532 : Nat := 30354034873773577728139

theorem tailTrace_598532 : CollatzResearch.WordTrace tailWord_598532 prefixEnd_598532 30354034873773577728139 := by
  unfold tailWord_598532
  simp only [CollatzResearch.WordTrace]
  refine ⟨10915127733814129986234925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14553503645085506648313233 10915127733814129986234925)
  ·
    refine ⟨4093172900180298744838097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10915127733814129986234925 4093172900180298744838097)
    ·
      refine ⟨3069879675135224058628573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4093172900180298744838097 3069879675135224058628573)
      ·
        refine ⟨1151204878175709021985715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3069879675135224058628573 1151204878175709021985715)
        ·
          refine ⟨1726807317263563532978573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1151204878175709021985715 1726807317263563532978573)
          ·
            refine ⟨647552743973836324866965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1726807317263563532978573 647552743973836324866965)
            ·
              refine ⟨30354034873773577728139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 647552743973836324866965 30354034873773577728139)
              ·
                rfl

theorem cell20_598532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 6].length) (baseStart_598532 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_598532 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_598532 prefixEnd_598532 := by exact prefixLift 598532
  have htrace : WordTrace (prefixWord ++ tailWord_598532) baseStart_598532 baseEnd_598532 := by
    simpa [prefixWord, tailWord_598532, baseEnd_598532] using wordTrace_append hprefix tailTrace_598532
  have hstable : (prefixWord ++ tailWord_598532).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598532).length < 2 ^ (prefixWord ++ tailWord_598532).sum := by decide
  have hdescent : baseEnd_598532 < baseStart_598532 := by decide
  rcases family_descends (prefixWord ++ tailWord_598532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598556 : List Nat := [2, 2, 3, 1, 2, 2, 4, 1, 3]
def baseStart_598556 : Nat := 118140960795 + 598556 * 2 ^ 59
def prefixEnd_598556 : Nat := 4983230072969 + 3 ^ 40 * 598556 * 2
def baseEnd_598556 : Nat := 273197268117924782753153

theorem tailTrace_598556 : CollatzResearch.WordTrace tailWord_598556 prefixEnd_598556 273197268117924782753153 := by
  unfold tailWord_598556
  simp only [CollatzResearch.WordTrace]
  refine ⟨10915565409770656035671761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14554087213027541380895681 10915565409770656035671761)
  ·
    refine ⟨8186674057327992026753821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10915565409770656035671761 8186674057327992026753821)
    ·
      refine ⟨3070002771497997010032683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8186674057327992026753821 3070002771497997010032683)
      ·
        refine ⟨4605004157246995515049025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3070002771497997010032683 4605004157246995515049025)
        ·
          refine ⟨3453753117935246636286769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4605004157246995515049025 3453753117935246636286769)
          ·
            refine ⟨2590314838451434977215077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3453753117935246636286769 2590314838451434977215077)
            ·
              refine ⟨485684032209644058227827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2590314838451434977215077 485684032209644058227827)
              ·
                refine ⟨728526048314466087341741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 485684032209644058227827 728526048314466087341741)
                ·
                  refine ⟨273197268117924782753153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 728526048314466087341741 273197268117924782753153)
                  ·
                    rfl

theorem cell20_598556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 4, 1, 3].length) (baseStart_598556 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_598556 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_598556 prefixEnd_598556 := by exact prefixLift 598556
  have htrace : WordTrace (prefixWord ++ tailWord_598556) baseStart_598556 baseEnd_598556 := by
    simpa [prefixWord, tailWord_598556, baseEnd_598556] using wordTrace_append hprefix tailTrace_598556
  have hstable : (prefixWord ++ tailWord_598556).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598556).length < 2 ^ (prefixWord ++ tailWord_598556).sum := by decide
  have hdescent : baseEnd_598556 < baseStart_598556 := by decide
  rcases family_descends (prefixWord ++ tailWord_598556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598646 : List Nat := [5, 1, 1, 2, 3, 1, 7]
def baseStart_598646 : Nat := 118140960795 + 598646 * 2 ^ 59
def prefixEnd_598646 : Nat := 4983230072969 + 3 ^ 40 * 598646 * 2
def baseEnd_598646 : Nat := 30359816285587163305865

theorem tailTrace_598646 : CollatzResearch.WordTrace tailWord_598646 prefixEnd_598646 30359816285587163305865 := by
  unfold tailWord_598646
  simp only [CollatzResearch.WordTrace]
  refine ⟨1364650836825953590132487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14556275592810171628079861 1364650836825953590132487)
  ·
    refine ⟨2046976255238930385198731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1364650836825953590132487 2046976255238930385198731)
    ·
      refine ⟨3070464382858395577798097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2046976255238930385198731 3070464382858395577798097)
      ·
        refine ⟨2302848287143796683348573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3070464382858395577798097 2302848287143796683348573)
        ·
          refine ⟨863568107678923756255715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2302848287143796683348573 863568107678923756255715)
          ·
            refine ⟨1295352161518385634383573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 863568107678923756255715 1295352161518385634383573)
            ·
              refine ⟨30359816285587163305865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1295352161518385634383573 30359816285587163305865)
              ·
                rfl

theorem cell20_598646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 7].length) (baseStart_598646 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_598646 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_598646 prefixEnd_598646 := by exact prefixLift 598646
  have htrace : WordTrace (prefixWord ++ tailWord_598646) baseStart_598646 baseEnd_598646 := by
    simpa [prefixWord, tailWord_598646, baseEnd_598646] using wordTrace_append hprefix tailTrace_598646
  have hstable : (prefixWord ++ tailWord_598646).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598646).length < 2 ^ (prefixWord ++ tailWord_598646).sum := by decide
  have hdescent : baseEnd_598646 < baseStart_598646 := by decide
  rcases family_descends (prefixWord ++ tailWord_598646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598653 : List Nat := [1, 4, 1, 1, 5, 1, 1, 1, 5]
def baseStart_598653 : Nat := 118140960795 + 598653 * 2 ^ 59
def prefixEnd_598653 : Nat := 4983230072969 + 3 ^ 40 * 598653 * 2
def baseEnd_598653 : Nat := 273241541561023556519423

theorem tailTrace_598653 : CollatzResearch.WordTrace tailWord_598653 prefixEnd_598653 273241541561023556519423 := by
  unfold tailWord_598653
  simp only [CollatzResearch.WordTrace]
  refine ⟨21834668700189897637624613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14556445800126598425083075 21834668700189897637624613)
  ·
    refine ⟨4094000381285605807054615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21834668700189897637624613 4094000381285605807054615)
    ·
      refine ⟨6141000571928408710581923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4094000381285605807054615 6141000571928408710581923)
      ·
        refine ⟨9211500857892613065872885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6141000571928408710581923 9211500857892613065872885)
        ·
          refine ⟨863578205427432474925583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9211500857892613065872885 863578205427432474925583)
          ·
            refine ⟨1295367308141148712388375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 863578205427432474925583 1295367308141148712388375)
            ·
              refine ⟨1943050962211723068582563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1295367308141148712388375 1943050962211723068582563)
              ·
                refine ⟨2914576443317584602873845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1943050962211723068582563 2914576443317584602873845)
                ·
                  refine ⟨273241541561023556519423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2914576443317584602873845 273241541561023556519423)
                  ·
                    rfl

theorem cell20_598653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 5].length) (baseStart_598653 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_598653 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_598653 prefixEnd_598653 := by exact prefixLift 598653
  have htrace : WordTrace (prefixWord ++ tailWord_598653) baseStart_598653 baseEnd_598653 := by
    simpa [prefixWord, tailWord_598653, baseEnd_598653] using wordTrace_append hprefix tailTrace_598653
  have hstable : (prefixWord ++ tailWord_598653).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598653).length < 2 ^ (prefixWord ++ tailWord_598653).sum := by decide
  have hdescent : baseEnd_598653 < baseStart_598653 := by decide
  rcases family_descends (prefixWord ++ tailWord_598653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598660 : List Nat := [2, 3, 2, 1, 3, 1, 1, 3, 4]
def baseStart_598660 : Nat := 118140960795 + 598660 * 2 ^ 59
def prefixEnd_598660 : Nat := 4983230072969 + 3 ^ 40 * 598660 * 2
def baseEnd_598660 : Nat := 273244736551762643286061

theorem tailTrace_598660 : CollatzResearch.WordTrace tailWord_598660 prefixEnd_598660 273244736551762643286061 := by
  unfold tailWord_598660
  simp only [CollatzResearch.WordTrace]
  refine ⟨10917462005582268916564717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14556616007443025222086289 10917462005582268916564717)
  ·
    refine ⟨4094048252093350843711769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10917462005582268916564717 4094048252093350843711769)
    ·
      refine ⟨3070536189070013132783827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4094048252093350843711769 3070536189070013132783827)
      ·
        refine ⟨4605804283605019699175741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3070536189070013132783827 4605804283605019699175741)
        ·
          refine ⟨1727176606351882387190903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4605804283605019699175741 1727176606351882387190903)
          ·
            refine ⟨2590764909527823580786355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1727176606351882387190903 2590764909527823580786355)
            ·
              refine ⟨3886147364291735371179533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2590764909527823580786355 3886147364291735371179533)
              ·
                refine ⟨1457305261609400764192325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3886147364291735371179533 1457305261609400764192325)
                ·
                  refine ⟨273244736551762643286061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1457305261609400764192325 273244736551762643286061)
                  ·
                    rfl

theorem cell20_598660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_598660 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_598660 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_598660 prefixEnd_598660 := by exact prefixLift 598660
  have htrace : WordTrace (prefixWord ++ tailWord_598660) baseStart_598660 baseEnd_598660 := by
    simpa [prefixWord, tailWord_598660, baseEnd_598660] using wordTrace_append hprefix tailTrace_598660
  have hstable : (prefixWord ++ tailWord_598660).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598660).length < 2 ^ (prefixWord ++ tailWord_598660).sum := by decide
  have hdescent : baseEnd_598660 < baseStart_598660 := by decide
  rcases family_descends (prefixWord ++ tailWord_598660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598670 : List Nat := [4, 1, 1, 3, 1, 1, 5, 1, 3]
def baseStart_598670 : Nat := 118140960795 + 598670 * 2 ^ 59
def prefixEnd_598670 : Nat := 4983230072969 + 3 ^ 40 * 598670 * 2
def baseEnd_598670 : Nat := 273249300824247052952687

theorem tailTrace_598670 : CollatzResearch.WordTrace tailWord_598670 prefixEnd_598670 273249300824247052952687 := by
  unfold tailWord_598670
  simp only [CollatzResearch.WordTrace]
  refine ⟨2729411092641038692624183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14556859160752206360662309 2729411092641038692624183)
  ·
    refine ⟨4094116638961558038936275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2729411092641038692624183 4094116638961558038936275)
    ·
      refine ⟨6141174958442337058404413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4094116638961558038936275 6141174958442337058404413)
      ·
        refine ⟨2302940609415876396901655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6141174958442337058404413 2302940609415876396901655)
        ·
          refine ⟨3454410914123814595352483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2302940609415876396901655 3454410914123814595352483)
          ·
            refine ⟨5181616371185721893028725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3454410914123814595352483 5181616371185721893028725)
            ·
              refine ⟨485776534798661427471443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5181616371185721893028725 485776534798661427471443)
              ·
                refine ⟨728664802197992141207165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 485776534798661427471443 728664802197992141207165)
                ·
                  refine ⟨273249300824247052952687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 728664802197992141207165 273249300824247052952687)
                  ·
                    rfl

theorem cell20_598670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 5, 1, 3].length) (baseStart_598670 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_598670 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_598670 prefixEnd_598670 := by exact prefixLift 598670
  have htrace : WordTrace (prefixWord ++ tailWord_598670) baseStart_598670 baseEnd_598670 := by
    simpa [prefixWord, tailWord_598670, baseEnd_598670] using wordTrace_append hprefix tailTrace_598670
  have hstable : (prefixWord ++ tailWord_598670).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598670).length < 2 ^ (prefixWord ++ tailWord_598670).sum := by decide
  have hdescent : baseEnd_598670 < baseStart_598670 := by decide
  rcases family_descends (prefixWord ++ tailWord_598670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598681 : List Nat := [1, 2, 1, 2, 1, 2, 3, 4, 4]
def baseStart_598681 : Nat := 118140960795 + 598681 * 2 ^ 59
def prefixEnd_598681 : Nat := 4983230072969 + 3 ^ 40 * 598681 * 2
def baseEnd_598681 : Nat := 273254321523979903585975

theorem tailTrace_598681 : CollatzResearch.WordTrace tailWord_598681 prefixEnd_598681 273254321523979903585975 := by
  unfold tailWord_598681
  simp only [CollatzResearch.WordTrace]
  refine ⟨21835689944088458419643897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14557126629392305613095931 21835689944088458419643897)
  ·
    refine ⟨16376767458066343814732923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21835689944088458419643897 16376767458066343814732923)
    ·
      refine ⟨24565151187099515722099385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16376767458066343814732923 24565151187099515722099385)
      ·
        refine ⟨18423863390324636791574539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24565151187099515722099385 18423863390324636791574539)
        ·
          refine ⟨27635795085486955187361809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18423863390324636791574539 27635795085486955187361809)
          ·
            refine ⟨20726846314115216390521357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27635795085486955187361809 20726846314115216390521357)
            ·
              refine ⟨7772567367793206146445509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20726846314115216390521357 7772567367793206146445509)
              ·
                refine ⟨1457356381461226152458533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7772567367793206146445509 1457356381461226152458533)
                ·
                  refine ⟨273254321523979903585975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1457356381461226152458533 273254321523979903585975)
                  ·
                    rfl

theorem cell20_598681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 4, 4].length) (baseStart_598681 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_598681 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_598681 prefixEnd_598681 := by exact prefixLift 598681
  have htrace : WordTrace (prefixWord ++ tailWord_598681) baseStart_598681 baseEnd_598681 := by
    simpa [prefixWord, tailWord_598681, baseEnd_598681] using wordTrace_append hprefix tailTrace_598681
  have hstable : (prefixWord ++ tailWord_598681).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598681).length < 2 ^ (prefixWord ++ tailWord_598681).sum := by decide
  have hdescent : baseEnd_598681 < baseStart_598681 := by decide
  rcases family_descends (prefixWord ++ tailWord_598681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598684 : List Nat := [2, 2, 3, 2, 2, 1, 4, 4]
def baseStart_598684 : Nat := 118140960795 + 598684 * 2 ^ 59
def prefixEnd_598684 : Nat := 4983230072969 + 3 ^ 40 * 598684 * 2
def baseEnd_598684 : Nat := 91085230268575075495321

theorem tailTrace_598684 : CollatzResearch.WordTrace tailWord_598684 prefixEnd_598684 91085230268575075495321 := by
  unfold tailWord_598684
  simp only [CollatzResearch.WordTrace]
  refine ⟨10917899681538794966001553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14557199575385059954668737 10917899681538794966001553)
  ·
    refine ⟨8188424761154096224501165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10917899681538794966001553 8188424761154096224501165)
    ·
      refine ⟨3070659285432786084187937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8188424761154096224501165 3070659285432786084187937)
      ·
        refine ⟨2302994464074589563140953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3070659285432786084187937 2302994464074589563140953)
        ·
          refine ⟨1727245848055942172355715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2302994464074589563140953 1727245848055942172355715)
          ·
            refine ⟨2590868772083913258533573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1727245848055942172355715 2590868772083913258533573)
            ·
              refine ⟨485787894765733735975045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2590868772083913258533573 485787894765733735975045)
              ·
                refine ⟨91085230268575075495321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 485787894765733735975045 91085230268575075495321)
                ·
                  rfl

theorem cell20_598684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 4, 4].length) (baseStart_598684 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_598684 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_598684 prefixEnd_598684 := by exact prefixLift 598684
  have htrace : WordTrace (prefixWord ++ tailWord_598684) baseStart_598684 baseEnd_598684 := by
    simpa [prefixWord, tailWord_598684, baseEnd_598684] using wordTrace_append hprefix tailTrace_598684
  have hstable : (prefixWord ++ tailWord_598684).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598684).length < 2 ^ (prefixWord ++ tailWord_598684).sum := by decide
  have hdescent : baseEnd_598684 < baseStart_598684 := by decide
  rcases family_descends (prefixWord ++ tailWord_598684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598721 : List Nat := [1, 2, 6, 2, 2, 1, 2, 1, 3]
def baseStart_598721 : Nat := 118140960795 + 598721 * 2 ^ 59
def prefixEnd_598721 : Nat := 4983230072969 + 3 ^ 40 * 598721 * 2
def baseEnd_598721 : Nat := 273272578613917542252479

theorem tailTrace_598721 : CollatzResearch.WordTrace tailWord_598721 prefixEnd_598721 273272578613917542252479 := by
  unfold tailWord_598721
  simp only [CollatzResearch.WordTrace]
  refine ⟨21837148863943545251100017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14558099242629030167400011 21837148863943545251100017)
  ·
    refine ⟨16377861647957658938325013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21837148863943545251100017 16377861647957658938325013)
    ·
      refine ⟨767712264748015262733985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 16377861647957658938325013 767712264748015262733985)
      ·
        refine ⟨575784198561011447050489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 767712264748015262733985 575784198561011447050489)
        ·
          refine ⟨431838148920758585287867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 575784198561011447050489 431838148920758585287867)
          ·
            refine ⟨647757223381137877931801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 431838148920758585287867 647757223381137877931801)
            ·
              refine ⟨485817917535853408448851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 647757223381137877931801 485817917535853408448851)
              ·
                refine ⟨728726876303780112673277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 485817917535853408448851 728726876303780112673277)
                ·
                  refine ⟨273272578613917542252479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 728726876303780112673277 273272578613917542252479)
                  ·
                    rfl

theorem cell20_598721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 2, 1, 3].length) (baseStart_598721 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_598721 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_598721 prefixEnd_598721 := by exact prefixLift 598721
  have htrace : WordTrace (prefixWord ++ tailWord_598721) baseStart_598721 baseEnd_598721 := by
    simpa [prefixWord, tailWord_598721, baseEnd_598721] using wordTrace_append hprefix tailTrace_598721
  have hstable : (prefixWord ++ tailWord_598721).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598721).length < 2 ^ (prefixWord ++ tailWord_598721).sum := by decide
  have hdescent : baseEnd_598721 < baseStart_598721 := by decide
  rcases family_descends (prefixWord ++ tailWord_598721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598767 : List Nat := [1, 1, 2, 1, 5, 3, 2, 2, 3]
def baseStart_598767 : Nat := 118140960795 + 598767 * 2 ^ 59
def prefixEnd_598767 : Nat := 4983230072969 + 3 ^ 40 * 598767 * 2
def baseEnd_598767 : Nat := 273293574267345826718957

theorem tailTrace_598767 : CollatzResearch.WordTrace tailWord_598767 prefixEnd_598767 273293574267345826718957 := by
  unfold tailWord_598767
  simp only [CollatzResearch.WordTrace]
  refine ⟨21838826621776895107274555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14559217747851263404849703 21838826621776895107274555)
  ·
    refine ⟨32758239932665342660911833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21838826621776895107274555 32758239932665342660911833)
    ·
      refine ⟨24568679949499006995683875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32758239932665342660911833 24568679949499006995683875)
      ·
        refine ⟨36853019924248510493525813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24568679949499006995683875 36853019924248510493525813)
        ·
          refine ⟨3454970617898297858768045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36853019924248510493525813 3454970617898297858768045)
          ·
            refine ⟨1295613981711861697038017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3454970617898297858768045 1295613981711861697038017)
            ·
              refine ⟨971710486283896272778513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1295613981711861697038017 971710486283896272778513)
              ·
                refine ⟨728782864712922204583885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 971710486283896272778513 728782864712922204583885)
                ·
                  refine ⟨273293574267345826718957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 728782864712922204583885 273293574267345826718957)
                  ·
                    rfl

theorem cell20_598767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 2, 3].length) (baseStart_598767 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_598767 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_598767 prefixEnd_598767 := by exact prefixLift 598767
  have htrace : WordTrace (prefixWord ++ tailWord_598767) baseStart_598767 baseEnd_598767 := by
    simpa [prefixWord, tailWord_598767, baseEnd_598767] using wordTrace_append hprefix tailTrace_598767
  have hstable : (prefixWord ++ tailWord_598767).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598767).length < 2 ^ (prefixWord ++ tailWord_598767).sum := by decide
  have hdescent : baseEnd_598767 < baseStart_598767 := by decide
  rcases family_descends (prefixWord ++ tailWord_598767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598770 : List Nat := [3, 2, 1, 3, 1, 2, 4, 2, 2]
def baseStart_598770 : Nat := 118140960795 + 598770 * 2 ^ 59
def prefixEnd_598770 : Nat := 4983230072969 + 3 ^ 40 * 598770 * 2
def baseEnd_598770 : Nat := 273294943549091149618945

theorem tailTrace_598770 : CollatzResearch.WordTrace tailWord_598770 prefixEnd_598770 273294943549091149618945 := by
  unfold tailWord_598770
  simp only [CollatzResearch.WordTrace]
  refine ⟨5459734010191506654908441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14559290693844017746422509 5459734010191506654908441)
  ·
    refine ⟨4094800507643629991181331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5459734010191506654908441 4094800507643629991181331)
    ·
      refine ⟨6142200761465444986771997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4094800507643629991181331 6142200761465444986771997)
      ·
        refine ⟨2303325285549541870039499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6142200761465444986771997 2303325285549541870039499)
        ·
          refine ⟨3454987928324312805059249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2303325285549541870039499 3454987928324312805059249)
          ·
            refine ⟨2591240946243234603794437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3454987928324312805059249 2591240946243234603794437)
            ·
              refine ⟨485857677420606488211457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2591240946243234603794437 485857677420606488211457)
              ·
                refine ⟨364393258065454866158593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 485857677420606488211457 364393258065454866158593)
                ·
                  refine ⟨273294943549091149618945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 364393258065454866158593 273294943549091149618945)
                  ·
                    rfl

theorem cell20_598770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 4, 2, 2].length) (baseStart_598770 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_598770 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_598770 prefixEnd_598770 := by exact prefixLift 598770
  have htrace : WordTrace (prefixWord ++ tailWord_598770) baseStart_598770 baseEnd_598770 := by
    simpa [prefixWord, tailWord_598770, baseEnd_598770] using wordTrace_append hprefix tailTrace_598770
  have hstable : (prefixWord ++ tailWord_598770).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598770).length < 2 ^ (prefixWord ++ tailWord_598770).sum := by decide
  have hdescent : baseEnd_598770 < baseStart_598770 := by decide
  rcases family_descends (prefixWord ++ tailWord_598770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598773 : List Nat := [1, 3, 6, 1, 2, 1, 1, 5]
def baseStart_598773 : Nat := 118140960795 + 598773 * 2 ^ 59
def prefixEnd_598773 : Nat := 4983230072969 + 3 ^ 40 * 598773 * 2
def baseEnd_598773 : Nat := 91098770943612157506311

theorem tailTrace_598773 : CollatzResearch.WordTrace tailWord_598773 prefixEnd_598773 91098770943612157506311 := by
  unfold tailWord_598773
  simp only [CollatzResearch.WordTrace]
  refine ⟨21839045459755158131992973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14559363639836772087995315 21839045459755158131992973)
  ·
    refine ⟨8189642047408184299497365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21839045459755158131992973 8189642047408184299497365)
    ·
      refine ⟨383889470972258639038939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 8189642047408184299497365 383889470972258639038939)
      ·
        refine ⟨575834206458387958558409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 383889470972258639038939 575834206458387958558409)
        ·
          refine ⟨431875654843790968918807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 575834206458387958558409 431875654843790968918807)
          ·
            refine ⟨647813482265686453378211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 431875654843790968918807 647813482265686453378211)
            ·
              refine ⟨971720223398529680067317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 647813482265686453378211 971720223398529680067317)
              ·
                refine ⟨91098770943612157506311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 971720223398529680067317 91098770943612157506311)
                ·
                  rfl

theorem cell20_598773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 5].length) (baseStart_598773 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_598773 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_598773 prefixEnd_598773 := by exact prefixLift 598773
  have htrace : WordTrace (prefixWord ++ tailWord_598773) baseStart_598773 baseEnd_598773 := by
    simpa [prefixWord, tailWord_598773, baseEnd_598773] using wordTrace_append hprefix tailTrace_598773
  have hstable : (prefixWord ++ tailWord_598773).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598773).length < 2 ^ (prefixWord ++ tailWord_598773).sum := by decide
  have hdescent : baseEnd_598773 < baseStart_598773 := by decide
  rcases family_descends (prefixWord ++ tailWord_598773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598774 : List Nat := [5, 1, 1, 1, 1, 2, 2, 3, 4]
def baseStart_598774 : Nat := 118140960795 + 598774 * 2 ^ 59
def prefixEnd_598774 : Nat := 4983230072969 + 3 ^ 40 * 598774 * 2
def baseEnd_598774 : Nat := 273296769258084913485595

theorem tailTrace_598774 : CollatzResearch.WordTrace tailWord_598774 prefixEnd_598774 273296769258084913485595 := by
  unfold tailWord_598774
  simp only [CollatzResearch.WordTrace]
  refine ⟨1364942620796970956423711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14559387955167690201852917 1364942620796970956423711)
  ·
    refine ⟨2047413931195456434635567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1364942620796970956423711 2047413931195456434635567)
    ·
      refine ⟨3071120896793184651953351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2047413931195456434635567 3071120896793184651953351)
      ·
        refine ⟨4606681345189776977930027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3071120896793184651953351 4606681345189776977930027)
        ·
          refine ⟨6910022017784665466895041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4606681345189776977930027 6910022017784665466895041)
          ·
            refine ⟨5182516513338499100171281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6910022017784665466895041 5182516513338499100171281)
            ·
              refine ⟨3886887385003874325128461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5182516513338499100171281 3886887385003874325128461)
              ·
                refine ⟨1457582769376452871923173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3886887385003874325128461 1457582769376452871923173)
                ·
                  refine ⟨273296769258084913485595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1457582769376452871923173 273296769258084913485595)
                  ·
                    rfl

theorem cell20_598774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_598774 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_598774 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_598774 prefixEnd_598774 := by exact prefixLift 598774
  have htrace : WordTrace (prefixWord ++ tailWord_598774) baseStart_598774 baseEnd_598774 := by
    simpa [prefixWord, tailWord_598774, baseEnd_598774] using wordTrace_append hprefix tailTrace_598774
  have hstable : (prefixWord ++ tailWord_598774).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598774).length < 2 ^ (prefixWord ++ tailWord_598774).sum := by decide
  have hdescent : baseEnd_598774 < baseStart_598774 := by decide
  rcases family_descends (prefixWord ++ tailWord_598774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598840 : List Nat := [2, 1, 2, 1, 3, 2, 2, 7]
def baseStart_598840 : Nat := 118140960795 + 598840 * 2 ^ 59
def prefixEnd_598840 : Nat := 4983230072969 + 3 ^ 40 * 598840 * 2
def baseEnd_598840 : Nat := 91108964485494005761775

theorem tailTrace_598840 : CollatzResearch.WordTrace tailWord_598840 prefixEnd_598840 91108964485494005761775 := by
  unfold tailWord_598840
  simp only [CollatzResearch.WordTrace]
  refine ⟨10920744575256214287340987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14560992767008285716454649 10920744575256214287340987)
  ·
    refine ⟨16381116862884321431011481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10920744575256214287340987 16381116862884321431011481)
    ·
      refine ⟨12285837647163241073258611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16381116862884321431011481 12285837647163241073258611)
      ·
        refine ⟨18428756470744861609887917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12285837647163241073258611 18428756470744861609887917)
        ·
          refine ⟨6910783676529323103707969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18428756470744861609887917 6910783676529323103707969)
          ·
            refine ⟨5183087757396992327780977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6910783676529323103707969 5183087757396992327780977)
            ·
              refine ⟨3887315818047744245835733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5183087757396992327780977 3887315818047744245835733)
              ·
                refine ⟨91108964485494005761775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3887315818047744245835733 91108964485494005761775)
                ·
                  rfl

theorem cell20_598840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 7].length) (baseStart_598840 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_598840 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_598840 prefixEnd_598840 := by exact prefixLift 598840
  have htrace : WordTrace (prefixWord ++ tailWord_598840) baseStart_598840 baseEnd_598840 := by
    simpa [prefixWord, tailWord_598840, baseEnd_598840] using wordTrace_append hprefix tailTrace_598840
  have hstable : (prefixWord ++ tailWord_598840).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598840).length < 2 ^ (prefixWord ++ tailWord_598840).sum := by decide
  have hdescent : baseEnd_598840 < baseStart_598840 := by decide
  rcases family_descends (prefixWord ++ tailWord_598840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598857 : List Nat := [1, 2, 1, 1, 2, 5, 4, 4]
def baseStart_598857 : Nat := 118140960795 + 598857 * 2 ^ 59
def prefixEnd_598857 : Nat := 4983230072969 + 3 ^ 40 * 598857 * 2
def baseEnd_598857 : Nat := 91111550906568504572863

theorem tailTrace_598857 : CollatzResearch.WordTrace tailWord_598857 prefixEnd_598857 91111550906568504572863 := by
  unfold tailWord_598857
  simp only [CollatzResearch.WordTrace]
  refine ⟨21842109191450840478050825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14561406127633893652033883 21842109191450840478050825)
  ·
    refine ⟨16381581893588130358538119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21842109191450840478050825 16381581893588130358538119)
    ·
      refine ⟨24572372840382195537807179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16381581893588130358538119 24572372840382195537807179)
      ·
        refine ⟨36858559260573293306710769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24572372840382195537807179 36858559260573293306710769)
        ·
          refine ⟨27643919445429969980033077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36858559260573293306710769 27643919445429969980033077)
          ·
            refine ⟨2591617448009059685628101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27643919445429969980033077 2591617448009059685628101)
            ·
              refine ⟨485928271501698691055269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2591617448009059685628101 485928271501698691055269)
              ·
                refine ⟨91111550906568504572863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 485928271501698691055269 91111550906568504572863)
                ·
                  rfl

theorem cell20_598857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 4, 4].length) (baseStart_598857 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_598857 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_598857 prefixEnd_598857 := by exact prefixLift 598857
  have htrace : WordTrace (prefixWord ++ tailWord_598857) baseStart_598857 baseEnd_598857 := by
    simpa [prefixWord, tailWord_598857, baseEnd_598857] using wordTrace_append hprefix tailTrace_598857
  have hstable : (prefixWord ++ tailWord_598857).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598857).length < 2 ^ (prefixWord ++ tailWord_598857).sum := by decide
  have hdescent : baseEnd_598857 < baseStart_598857 := by decide
  rcases family_descends (prefixWord ++ tailWord_598857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598884 : List Nat := [2, 3, 1, 1, 4, 2, 3, 2, 2]
def baseStart_598884 : Nat := 118140960795 + 598884 * 2 ^ 59
def prefixEnd_598884 : Nat := 4983230072969 + 3 ^ 40 * 598884 * 2
def baseEnd_598884 : Nat := 273346976255413419818479

theorem tailTrace_598884 : CollatzResearch.WordTrace tailWord_598884 prefixEnd_598884 273346976255413419818479 := by
  unfold tailWord_598884
  simp only [CollatzResearch.WordTrace]
  refine ⟨10921546981176512044641853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14562062641568682726189137 10921546981176512044641853)
  ·
    refine ⟨4095580117941192016740695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10921546981176512044641853 4095580117941192016740695)
    ·
      refine ⟨6143370176911788025111043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4095580117941192016740695 6143370176911788025111043)
      ·
        refine ⟨9215055265367682037666565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6143370176911788025111043 9215055265367682037666565)
        ·
          refine ⟨1727822862256440382062481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9215055265367682037666565 1727822862256440382062481)
          ·
            refine ⟨1295867146692330286546861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1727822862256440382062481 1295867146692330286546861)
            ·
              refine ⟨485950180009623857455073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1295867146692330286546861 485950180009623857455073)
              ·
                refine ⟨364462635007217893091305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 485950180009623857455073 364462635007217893091305)
                ·
                  refine ⟨273346976255413419818479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 364462635007217893091305 273346976255413419818479)
                  ·
                    rfl

theorem cell20_598884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 3, 2, 2].length) (baseStart_598884 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_598884 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_598884 prefixEnd_598884 := by exact prefixLift 598884
  have htrace : WordTrace (prefixWord ++ tailWord_598884) baseStart_598884 baseEnd_598884 := by
    simpa [prefixWord, tailWord_598884, baseEnd_598884] using wordTrace_append hprefix tailTrace_598884
  have hstable : (prefixWord ++ tailWord_598884).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598884).length < 2 ^ (prefixWord ++ tailWord_598884).sum := by decide
  have hdescent : baseEnd_598884 < baseStart_598884 := by decide
  rcases family_descends (prefixWord ++ tailWord_598884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598888 : List Nat := [2, 1, 4, 2, 1, 2, 3, 1, 4]
def baseStart_598888 : Nat := 118140960795 + 598888 * 2 ^ 59
def prefixEnd_598888 : Nat := 4983230072969 + 3 ^ 40 * 598888 * 2
def baseEnd_598888 : Nat := 273348801964407183685129

theorem tailTrace_598888 : CollatzResearch.WordTrace tailWord_598888 prefixEnd_598888 273348801964407183685129 := by
  unfold tailWord_598888
  simp only [CollatzResearch.WordTrace]
  refine ⟨10921619927169266386214659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14562159902892355181619545 10921619927169266386214659)
  ·
    refine ⟨16382429890753899579321989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10921619927169266386214659 16382429890753899579321989)
    ·
      refine ⟨3071705604516356171122873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16382429890753899579321989 3071705604516356171122873)
      ·
        refine ⟨2303779203387267128342155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3071705604516356171122873 2303779203387267128342155)
        ·
          refine ⟨3455668805080900692513233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2303779203387267128342155 3455668805080900692513233)
          ·
            refine ⟨2591751603810675519384925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3455668805080900692513233 2591751603810675519384925)
            ·
              refine ⟨971906851429003319769347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2591751603810675519384925 971906851429003319769347)
              ·
                refine ⟨1457860277143504979654021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 971906851429003319769347 1457860277143504979654021)
                ·
                  refine ⟨273348801964407183685129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1457860277143504979654021 273348801964407183685129)
                  ·
                    rfl

theorem cell20_598888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 1, 4].length) (baseStart_598888 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_598888 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_598888 prefixEnd_598888 := by exact prefixLift 598888
  have htrace : WordTrace (prefixWord ++ tailWord_598888) baseStart_598888 baseEnd_598888 := by
    simpa [prefixWord, tailWord_598888, baseEnd_598888] using wordTrace_append hprefix tailTrace_598888
  have hstable : (prefixWord ++ tailWord_598888).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598888).length < 2 ^ (prefixWord ++ tailWord_598888).sum := by decide
  have hdescent : baseEnd_598888 < baseStart_598888 := by decide
  rcases family_descends (prefixWord ++ tailWord_598888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598894 : List Nat := [4, 1, 2, 3, 3, 1, 2, 1, 3]
def baseStart_598894 : Nat := 118140960795 + 598894 * 2 ^ 59
def prefixEnd_598894 : Nat := 4983230072969 + 3 ^ 40 * 598894 * 2
def baseEnd_598894 : Nat := 273351540527897829485105

theorem tailTrace_598894 : CollatzResearch.WordTrace tailWord_598894 prefixEnd_598894 273351540527897829485105 := by
  unfold tailWord_598894
  simp only [CollatzResearch.WordTrace]
  refine ⟨2730432336539599474643467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14562305794877863864765157 2730432336539599474643467)
  ·
    refine ⟨4095648504809399211965201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2730432336539599474643467 4095648504809399211965201)
    ·
      refine ⟨3071736378607049408973901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4095648504809399211965201 3071736378607049408973901)
      ·
        refine ⟨1151901141977643528365213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3071736378607049408973901 1151901141977643528365213)
        ·
          refine ⟨431962928241616323136955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1151901141977643528365213 431962928241616323136955)
          ·
            refine ⟨647944392362424484705433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 431962928241616323136955 647944392362424484705433)
            ·
              refine ⟨485958294271818363529075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 647944392362424484705433 485958294271818363529075)
              ·
                refine ⟨728937441407727545293613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 485958294271818363529075 728937441407727545293613)
                ·
                  refine ⟨273351540527897829485105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 728937441407727545293613 273351540527897829485105)
                  ·
                    rfl

theorem cell20_598894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 2, 1, 3].length) (baseStart_598894 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_598894 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_598894 prefixEnd_598894 := by exact prefixLift 598894
  have htrace : WordTrace (prefixWord ++ tailWord_598894) baseStart_598894 baseEnd_598894 := by
    simpa [prefixWord, tailWord_598894, baseEnd_598894] using wordTrace_append hprefix tailTrace_598894
  have hstable : (prefixWord ++ tailWord_598894).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598894).length < 2 ^ (prefixWord ++ tailWord_598894).sum := by decide
  have hdescent : baseEnd_598894 < baseStart_598894 := by decide
  rcases family_descends (prefixWord ++ tailWord_598894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598909 : List Nat := [1, 4, 1, 1, 2, 1, 2, 4, 4]
def baseStart_598909 : Nat := 118140960795 + 598909 * 2 ^ 59
def prefixEnd_598909 : Nat := 4983230072969 + 3 ^ 40 * 598909 * 2
def baseEnd_598909 : Nat := 273358386936624443985043

theorem tailTrace_598909 : CollatzResearch.WordTrace tailWord_598909 prefixEnd_598909 273358386936624443985043 := by
  unfold tailWord_598909
  simp only [CollatzResearch.WordTrace]
  refine ⟨21844005787262453358943781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14562670524841635572629187 21844005787262453358943781)
  ·
    refine ⟨4095751085111710004801959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21844005787262453358943781 4095751085111710004801959)
    ·
      refine ⟨6143626627667565007202939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4095751085111710004801959 6143626627667565007202939)
      ·
        refine ⟨9215439941501347510804409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6143626627667565007202939 9215439941501347510804409)
        ·
          refine ⟨6911579956126010633103307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9215439941501347510804409 6911579956126010633103307)
          ·
            refine ⟨10367369934189015949654961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6911579956126010633103307 10367369934189015949654961)
            ·
              refine ⟨7775527450641761962241221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10367369934189015949654961 7775527450641761962241221)
              ·
                refine ⟨1457911396995330367920229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7775527450641761962241221 1457911396995330367920229)
                ·
                  refine ⟨273358386936624443985043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1457911396995330367920229 273358386936624443985043)
                  ·
                    rfl

theorem cell20_598909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_598909 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_598909 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_598909 prefixEnd_598909 := by exact prefixLift 598909
  have htrace : WordTrace (prefixWord ++ tailWord_598909) baseStart_598909 baseEnd_598909 := by
    simpa [prefixWord, tailWord_598909, baseEnd_598909] using wordTrace_append hprefix tailTrace_598909
  have hstable : (prefixWord ++ tailWord_598909).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598909).length < 2 ^ (prefixWord ++ tailWord_598909).sum := by decide
  have hdescent : baseEnd_598909 < baseStart_598909 := by decide
  rcases family_descends (prefixWord ++ tailWord_598909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598923 : List Nat := [1, 1, 1, 1, 4, 2, 2, 1, 7]
def baseStart_598923 : Nat := 118140960795 + 598923 * 2 ^ 59
def prefixEnd_598923 : Nat := 4983230072969 + 3 ^ 40 * 598923 * 2
def baseEnd_598923 : Nat := 273364776918102617518319

theorem tailTrace_598923 : CollatzResearch.WordTrace tailWord_598923 prefixEnd_598923 273364776918102617518319 := by
  unfold tailWord_598923
  simp only [CollatzResearch.WordTrace]
  refine ⟨21844516409211733749953423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14563010939474489166635615 21844516409211733749953423)
  ·
    refine ⟨32766774613817600624930135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21844516409211733749953423 32766774613817600624930135)
    ·
      refine ⟨49150161920726400937395203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32766774613817600624930135 49150161920726400937395203)
      ·
        refine ⟨73725242881089601406092805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49150161920726400937395203 73725242881089601406092805)
        ·
          refine ⟨13823483040204300263642401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73725242881089601406092805 13823483040204300263642401)
          ·
            refine ⟨10367612280153225197731801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13823483040204300263642401 10367612280153225197731801)
            ·
              refine ⟨7775709210114918898298851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10367612280153225197731801 7775709210114918898298851)
              ·
                refine ⟨11663563815172378347448277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7775709210114918898298851 11663563815172378347448277)
                ·
                  refine ⟨273364776918102617518319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11663563815172378347448277 273364776918102617518319)
                  ·
                    rfl

theorem cell20_598923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 7].length) (baseStart_598923 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_598923 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_598923 prefixEnd_598923 := by exact prefixLift 598923
  have htrace : WordTrace (prefixWord ++ tailWord_598923) baseStart_598923 baseEnd_598923 := by
    simpa [prefixWord, tailWord_598923, baseEnd_598923] using wordTrace_append hprefix tailTrace_598923
  have hstable : (prefixWord ++ tailWord_598923).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598923).length < 2 ^ (prefixWord ++ tailWord_598923).sum := by decide
  have hdescent : baseEnd_598923 < baseStart_598923 := by decide
  rcases family_descends (prefixWord ++ tailWord_598923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598943 : List Nat := [1, 1, 2, 5, 2, 2, 1, 4, 2]
def baseStart_598943 : Nat := 118140960795 + 598943 * 2 ^ 59
def prefixEnd_598943 : Nat := 4983230072969 + 3 ^ 40 * 598943 * 2
def baseEnd_598943 : Nat := 273373905463071436851571

theorem tailTrace_598943 : CollatzResearch.WordTrace tailWord_598943 prefixEnd_598943 273373905463071436851571 := by
  unfold tailWord_598943
  simp only [CollatzResearch.WordTrace]
  refine ⟨21845245869139277165681483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14563497246092851443787655 21845245869139277165681483)
  ·
    refine ⟨32767868803708915748522225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21845245869139277165681483 32767868803708915748522225)
    ·
      refine ⟨24575901602781686811391669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32767868803708915748522225 24575901602781686811391669)
      ·
        refine ⟨2303990775260783138567969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24575901602781686811391669 2303990775260783138567969)
        ·
          refine ⟨1727993081445587353925977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2303990775260783138567969 1727993081445587353925977)
          ·
            refine ⟨1295994811084190515444483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1727993081445587353925977 1295994811084190515444483)
            ·
              refine ⟨1943992216626285773166725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1295994811084190515444483 1943992216626285773166725)
              ·
                refine ⟨364498540617428582468761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1943992216626285773166725 364498540617428582468761)
                ·
                  refine ⟨273373905463071436851571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 364498540617428582468761 273373905463071436851571)
                  ·
                    rfl

theorem cell20_598943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 4, 2].length) (baseStart_598943 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_598943 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_598943 prefixEnd_598943 := by exact prefixLift 598943
  have htrace : WordTrace (prefixWord ++ tailWord_598943) baseStart_598943 baseEnd_598943 := by
    simpa [prefixWord, tailWord_598943, baseEnd_598943] using wordTrace_append hprefix tailTrace_598943
  have hstable : (prefixWord ++ tailWord_598943).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598943).length < 2 ^ (prefixWord ++ tailWord_598943).sum := by decide
  have hdescent : baseEnd_598943 < baseStart_598943 := by decide
  rcases family_descends (prefixWord ++ tailWord_598943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598998 : List Nat := [5, 2, 1, 1, 2, 1, 2, 4, 2]
def baseStart_598998 : Nat := 118140960795 + 598998 * 2 ^ 59
def prefixEnd_598998 : Nat := 4983230072969 + 3 ^ 40 * 598998 * 2
def baseEnd_598998 : Nat := 273399008961735690018013

theorem tailTrace_598998 : CollatzResearch.WordTrace tailWord_598998 prefixEnd_598998 273399008961735690018013 := by
  unfold tailWord_598998
  simp only [CollatzResearch.WordTrace]
  refine ⟨1365453242746251347433353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14564834589293347705955765 1365453242746251347433353)
  ·
    refine ⟨1024089932059688510575015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1365453242746251347433353 1024089932059688510575015)
    ·
      refine ⟨1536134898089532765862523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1024089932059688510575015 1536134898089532765862523)
      ·
        refine ⟨2304202347134299148793785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1536134898089532765862523 2304202347134299148793785)
        ·
          refine ⟨1728151760350724361595339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2304202347134299148793785 1728151760350724361595339)
          ·
            refine ⟨2592227640526086542393009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1728151760350724361595339 2592227640526086542393009)
            ·
              refine ⟨1944170730394564906794757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2592227640526086542393009 1944170730394564906794757)
              ·
                refine ⟨364532011948980920024017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1944170730394564906794757 364532011948980920024017)
                ·
                  refine ⟨273399008961735690018013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 364532011948980920024017 273399008961735690018013)
                  ·
                    rfl

theorem cell20_598998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_598998 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_598998 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_598998 prefixEnd_598998 := by exact prefixLift 598998
  have htrace : WordTrace (prefixWord ++ tailWord_598998) baseStart_598998 baseEnd_598998 := by
    simpa [prefixWord, tailWord_598998, baseEnd_598998] using wordTrace_append hprefix tailTrace_598998
  have hstable : (prefixWord ++ tailWord_598998).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598998).length < 2 ^ (prefixWord ++ tailWord_598998).sum := by decide
  have hdescent : baseEnd_598998 < baseStart_598998 := by decide
  rcases family_descends (prefixWord ++ tailWord_598998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599002 : List Nat := [3, 1, 1, 2, 4, 2, 2, 1, 4]
def baseStart_599002 : Nat := 118140960795 + 599002 * 2 ^ 59
def prefixEnd_599002 : Nat := 4983230072969 + 3 ^ 40 * 599002 * 2
def baseEnd_599002 : Nat := 273400834670729453884663

theorem tailTrace_599002 : CollatzResearch.WordTrace tailWord_599002 prefixEnd_599002 273400834670729453884663 := by
  unfold tailWord_599002
  simp only [CollatzResearch.WordTrace]
  refine ⟨5461849443981382560519815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14564931850617020161386173 5461849443981382560519815)
  ·
    refine ⟨8192774165972073840779723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5461849443981382560519815 8192774165972073840779723)
    ·
      refine ⟨12289161248958110761169585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8192774165972073840779723 12289161248958110761169585)
      ·
        refine ⟨9216870936718583070877189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12289161248958110761169585 9216870936718583070877189)
        ·
          refine ⟨1728163300634734325789473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9216870936718583070877189 1728163300634734325789473)
          ·
            refine ⟨1296122475476050744342105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1728163300634734325789473 1296122475476050744342105)
            ·
              refine ⟨972091856607038058256579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1296122475476050744342105 972091856607038058256579)
              ·
                refine ⟨1458137784910557087384869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 972091856607038058256579 1458137784910557087384869)
                ·
                  refine ⟨273400834670729453884663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1458137784910557087384869 273400834670729453884663)
                  ·
                    rfl

theorem cell20_599002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 1, 4].length) (baseStart_599002 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_599002 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_599002 prefixEnd_599002 := by exact prefixLift 599002
  have htrace : WordTrace (prefixWord ++ tailWord_599002) baseStart_599002 baseEnd_599002 := by
    simpa [prefixWord, tailWord_599002, baseEnd_599002] using wordTrace_append hprefix tailTrace_599002
  have hstable : (prefixWord ++ tailWord_599002).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599002).length < 2 ^ (prefixWord ++ tailWord_599002).sum := by decide
  have hdescent : baseEnd_599002 < baseStart_599002 := by decide
  rcases family_descends (prefixWord ++ tailWord_599002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599016 : List Nat := [2, 1, 4, 1, 1, 1, 2, 5, 3]
def baseStart_599016 : Nat := 118140960795 + 599016 * 2 ^ 59
def prefixEnd_599016 : Nat := 4983230072969 + 3 ^ 40 * 599016 * 2
def baseEnd_599016 : Nat := 273407224652207627417939

theorem tailTrace_599016 : CollatzResearch.WordTrace tailWord_599016 prefixEnd_599016 273407224652207627417939 := by
  unfold tailWord_599016
  simp only [CollatzResearch.WordTrace]
  refine ⟨10923954198937405316544451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14565272265249873755392601 10923954198937405316544451)
  ·
    refine ⟨16385931298406107974816677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10923954198937405316544451 16385931298406107974816677)
    ·
      refine ⟨3072362118451145245278127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16385931298406107974816677 3072362118451145245278127)
      ·
        refine ⟨4608543177676717867917191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3072362118451145245278127 4608543177676717867917191)
        ·
          refine ⟨6912814766515076801875787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4608543177676717867917191 6912814766515076801875787)
          ·
            refine ⟨10369222149772615202813681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6912814766515076801875787 10369222149772615202813681)
            ·
              refine ⟨7776916612329461402110261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10369222149772615202813681 7776916612329461402110261)
              ·
                refine ⟨729085932405887006447837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7776916612329461402110261 729085932405887006447837)
                ·
                  refine ⟨273407224652207627417939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 729085932405887006447837 273407224652207627417939)
                  ·
                    rfl

theorem cell20_599016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 5, 3].length) (baseStart_599016 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_599016 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_599016 prefixEnd_599016 := by exact prefixLift 599016
  have htrace : WordTrace (prefixWord ++ tailWord_599016) baseStart_599016 baseEnd_599016 := by
    simpa [prefixWord, tailWord_599016, baseEnd_599016] using wordTrace_append hprefix tailTrace_599016
  have hstable : (prefixWord ++ tailWord_599016).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599016).length < 2 ^ (prefixWord ++ tailWord_599016).sum := by decide
  have hdescent : baseEnd_599016 < baseStart_599016 := by decide
  rcases family_descends (prefixWord ++ tailWord_599016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599023 : List Nat := [1, 1, 2, 1, 4, 3, 2, 2, 4]
def baseStart_599023 : Nat := 118140960795 + 599023 * 2 ^ 59
def prefixEnd_599023 : Nat := 4983230072969 + 3 ^ 40 * 599023 * 2
def baseEnd_599023 : Nat := 273410419642946714184577

theorem tailTrace_599023 : CollatzResearch.WordTrace tailWord_599023 prefixEnd_599023 273410419642946714184577 := by
  unfold tailWord_599023
  simp only [CollatzResearch.WordTrace]
  refine ⟨21848163708849450828593723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14565442472566300552395815 21848163708849450828593723)
  ·
    refine ⟨32772245563274176242890585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21848163708849450828593723 32772245563274176242890585)
    ·
      refine ⟨24579184172455632182167939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32772245563274176242890585 24579184172455632182167939)
      ·
        refine ⟨36868776258683448273251909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24579184172455632182167939 36868776258683448273251909)
        ·
          refine ⟨6912895548503146551234733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36868776258683448273251909 6912895548503146551234733)
          ·
            refine ⟨2592335830688679956713025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6912895548503146551234733 2592335830688679956713025)
            ·
              refine ⟨1944251873016509967534769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2592335830688679956713025 1944251873016509967534769)
              ·
                refine ⟨1458188904762382475651077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1944251873016509967534769 1458188904762382475651077)
                ·
                  refine ⟨273410419642946714184577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1458188904762382475651077 273410419642946714184577)
                  ·
                    rfl

theorem cell20_599023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 2, 4].length) (baseStart_599023 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_599023 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_599023 prefixEnd_599023 := by exact prefixLift 599023
  have htrace : WordTrace (prefixWord ++ tailWord_599023) baseStart_599023 baseEnd_599023 := by
    simpa [prefixWord, tailWord_599023, baseEnd_599023] using wordTrace_append hprefix tailTrace_599023
  have hstable : (prefixWord ++ tailWord_599023).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599023).length < 2 ^ (prefixWord ++ tailWord_599023).sum := by decide
  have hdescent : baseEnd_599023 < baseStart_599023 := by decide
  rcases family_descends (prefixWord ++ tailWord_599023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599026 : List Nat := [3, 2, 1, 5, 1, 1, 1, 6]
def baseStart_599026 : Nat := 118140960795 + 599026 * 2 ^ 59
def prefixEnd_599026 : Nat := 4983230072969 + 3 ^ 40 * 599026 * 2
def baseEnd_599026 : Nat := 91137262974897345694855

theorem tailTrace_599026 : CollatzResearch.WordTrace tailWord_599026 prefixEnd_599026 91137262974897345694855 := by
  unfold tailWord_599026
  simp only [CollatzResearch.WordTrace]
  refine ⟨5462068281959645585238233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14565515418559054893968621 5462068281959645585238233)
  ·
    refine ⟨4096551211469734188928675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5462068281959645585238233 4096551211469734188928675)
    ·
      refine ⟨6144826817204601283393013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4096551211469734188928675 6144826817204601283393013)
      ·
        refine ⟨576077514112931370318095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6144826817204601283393013 576077514112931370318095)
        ·
          refine ⟨864116271169397055477143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 576077514112931370318095 864116271169397055477143)
          ·
            refine ⟨1296174406754095583215715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 864116271169397055477143 1296174406754095583215715)
            ·
              refine ⟨1944261610131143374823573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1296174406754095583215715 1944261610131143374823573)
              ·
                refine ⟨91137262974897345694855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1944261610131143374823573 91137262974897345694855)
                ·
                  rfl

theorem cell20_599026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 6].length) (baseStart_599026 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_599026 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_599026 prefixEnd_599026 := by exact prefixLift 599026
  have htrace : WordTrace (prefixWord ++ tailWord_599026) baseStart_599026 baseEnd_599026 := by
    simpa [prefixWord, tailWord_599026, baseEnd_599026] using wordTrace_append hprefix tailTrace_599026
  have hstable : (prefixWord ++ tailWord_599026).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599026).length < 2 ^ (prefixWord ++ tailWord_599026).sum := by decide
  have hdescent : baseEnd_599026 < baseStart_599026 := by decide
  rcases family_descends (prefixWord ++ tailWord_599026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599028 : List Nat := [2, 6, 2, 1, 2, 1, 1, 3, 2]
def baseStart_599028 : Nat := 118140960795 + 599028 * 2 ^ 59
def prefixEnd_599028 : Nat := 4983230072969 + 3 ^ 40 * 599028 * 2
def baseEnd_599028 : Nat := 273412701779188919017891

theorem tailTrace_599028 : CollatzResearch.WordTrace tailWord_599028 prefixEnd_599028 273412701779188919017891 := by
  unfold tailWord_599028
  simp only [CollatzResearch.WordTrace]
  refine ⟨10924173036915668341262869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14565564049220891121683825 10924173036915668341262869)
  ·
    refine ⟨512070611105421953496697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 10924173036915668341262869 512070611105421953496697)
    ·
      refine ⟨384052958329066465122523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 512070611105421953496697 384052958329066465122523)
      ·
        refine ⟨576079437493599697683785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 384052958329066465122523 576079437493599697683785)
        ·
          refine ⟨432059578120199773262839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 576079437493599697683785 432059578120199773262839)
          ·
            refine ⟨648089367180299659894259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 432059578120199773262839 648089367180299659894259)
            ·
              refine ⟨972134050770449489841389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 648089367180299659894259 972134050770449489841389)
              ·
                refine ⟨364550269038918558690521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 972134050770449489841389 364550269038918558690521)
                ·
                  refine ⟨273412701779188919017891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 364550269038918558690521 273412701779188919017891)
                  ·
                    rfl

theorem cell20_599028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_599028 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_599028 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_599028 prefixEnd_599028 := by exact prefixLift 599028
  have htrace : WordTrace (prefixWord ++ tailWord_599028) baseStart_599028 baseEnd_599028 := by
    simpa [prefixWord, tailWord_599028, baseEnd_599028] using wordTrace_append hprefix tailTrace_599028
  have hstable : (prefixWord ++ tailWord_599028).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599028).length < 2 ^ (prefixWord ++ tailWord_599028).sum := by decide
  have hdescent : baseEnd_599028 < baseStart_599028 := by decide
  rcases family_descends (prefixWord ++ tailWord_599028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599054 : List Nat := [4, 1, 1, 2, 2, 2, 2, 1, 5]
def baseStart_599054 : Nat := 118140960795 + 599054 * 2 ^ 59
def prefixEnd_599054 : Nat := 4983230072969 + 3 ^ 40 * 599054 * 2
def baseEnd_599054 : Nat := 273424568887648384151117

theorem tailTrace_599054 : CollatzResearch.WordTrace tailWord_599054 prefixEnd_599054 273424568887648384151117 := by
  unfold tailWord_599054
  simp only [CollatzResearch.WordTrace]
  refine ⟨2731161796467142890371527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14566196247824762081981477 2731161796467142890371527)
  ·
    refine ⟨4096742694700714335557291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2731161796467142890371527 4096742694700714335557291)
    ·
      refine ⟨6145114042051071503335937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4096742694700714335557291 6145114042051071503335937)
      ·
        refine ⟨4608835531538303627501953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6145114042051071503335937 4608835531538303627501953)
        ·
          refine ⟨3456626648653727720626465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4608835531538303627501953 3456626648653727720626465)
          ·
            refine ⟨2592469986490295790469849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3456626648653727720626465 2592469986490295790469849)
            ·
              refine ⟨1944352489867721842852387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2592469986490295790469849 1944352489867721842852387)
              ·
                refine ⟨2916528734801582764278581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1944352489867721842852387 2916528734801582764278581)
                ·
                  refine ⟨273424568887648384151117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2916528734801582764278581 273424568887648384151117)
                  ·
                    rfl

theorem cell20_599054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_599054 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_599054 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_599054 prefixEnd_599054 := by exact prefixLift 599054
  have htrace : WordTrace (prefixWord ++ tailWord_599054) baseStart_599054 baseEnd_599054 := by
    simpa [prefixWord, tailWord_599054, baseEnd_599054] using wordTrace_append hprefix tailTrace_599054
  have hstable : (prefixWord ++ tailWord_599054).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599054).length < 2 ^ (prefixWord ++ tailWord_599054).sum := by decide
  have hdescent : baseEnd_599054 < baseStart_599054 := by decide
  rcases family_descends (prefixWord ++ tailWord_599054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599071 : List Nat := [1, 1, 2, 4, 1, 3, 4, 1, 3]
def baseStart_599071 : Nat := 118140960795 + 599071 * 2 ^ 59
def prefixEnd_599071 : Nat := 4983230072969 + 3 ^ 40 * 599071 * 2
def baseEnd_599071 : Nat := 273432328150871880584381

theorem tailTrace_599071 : CollatzResearch.WordTrace tailWord_599071 prefixEnd_599071 273432328150871880584381 := by
  unfold tailWord_599071
  simp only [CollatzResearch.WordTrace]
  refine ⟨21849914412675555026341067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14566609608450370017560711 21849914412675555026341067)
  ·
    refine ⟨32774871619013332539511601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21849914412675555026341067 32774871619013332539511601)
    ·
      refine ⟨24581153714259999404633701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32774871619013332539511601 24581153714259999404633701)
      ·
        refine ⟨4608966321423749888368819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24581153714259999404633701 4608966321423749888368819)
        ·
          refine ⟨6913449482135624832553229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4608966321423749888368819 6913449482135624832553229)
          ·
            refine ⟨2592543555800859312207461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6913449482135624832553229 2592543555800859312207461)
            ·
              refine ⟨486101916712661121038899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2592543555800859312207461 486101916712661121038899)
              ·
                refine ⟨729152875068991681558349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 486101916712661121038899 729152875068991681558349)
                ·
                  refine ⟨273432328150871880584381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 729152875068991681558349 273432328150871880584381)
                  ·
                    rfl

theorem cell20_599071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 4, 1, 3].length) (baseStart_599071 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_599071 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_599071 prefixEnd_599071 := by exact prefixLift 599071
  have htrace : WordTrace (prefixWord ++ tailWord_599071) baseStart_599071 baseEnd_599071 := by
    simpa [prefixWord, tailWord_599071, baseEnd_599071] using wordTrace_append hprefix tailTrace_599071
  have hstable : (prefixWord ++ tailWord_599071).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599071).length < 2 ^ (prefixWord ++ tailWord_599071).sum := by decide
  have hdescent : baseEnd_599071 < baseStart_599071 := by decide
  rcases family_descends (prefixWord ++ tailWord_599071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599120 : List Nat := [2, 1, 1, 1, 1, 3, 1, 2, 8]
def baseStart_599120 : Nat := 118140960795 + 599120 * 2 ^ 59
def prefixEnd_599120 : Nat := 4983230072969 + 3 ^ 40 * 599120 * 2
def baseEnd_599120 : Nat := 273454693086045487950847

theorem tailTrace_599120 : CollatzResearch.WordTrace tailWord_599120 prefixEnd_599120 273454693086045487950847 := by
  unfold tailWord_599120
  simp only [CollatzResearch.WordTrace]
  refine ⟨10925850794749018197437407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14567801059665357596583209 10925850794749018197437407)
  ·
    refine ⟨16388776192123527296156111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10925850794749018197437407 16388776192123527296156111)
    ·
      refine ⟨24583164288185290944234167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16388776192123527296156111 24583164288185290944234167)
      ·
        refine ⟨36874746432277936416351251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24583164288185290944234167 36874746432277936416351251)
        ·
          refine ⟨55312119648416904624526877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36874746432277936416351251 55312119648416904624526877)
          ·
            refine ⟨20742044868156339234197579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55312119648416904624526877 20742044868156339234197579)
            ·
              refine ⟨31113067302234508851296369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20742044868156339234197579 31113067302234508851296369)
              ·
                refine ⟨23334800476675881638472277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31113067302234508851296369 23334800476675881638472277)
                ·
                  refine ⟨273454693086045487950847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23334800476675881638472277 273454693086045487950847)
                  ·
                    rfl

theorem cell20_599120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 8].length) (baseStart_599120 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_599120 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_599120 prefixEnd_599120 := by exact prefixLift 599120
  have htrace : WordTrace (prefixWord ++ tailWord_599120) baseStart_599120 baseEnd_599120 := by
    simpa [prefixWord, tailWord_599120, baseEnd_599120] using wordTrace_append hprefix tailTrace_599120
  have hstable : (prefixWord ++ tailWord_599120).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599120).length < 2 ^ (prefixWord ++ tailWord_599120).sum := by decide
  have hdescent : baseEnd_599120 < baseStart_599120 := by decide
  rcases family_descends (prefixWord ++ tailWord_599120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599133 : List Nat := [1, 4, 4, 1, 2, 1, 1, 2, 4]
def baseStart_599133 : Nat := 118140960795 + 599133 * 2 ^ 59
def prefixEnd_599133 : Nat := 4983230072969 + 3 ^ 40 * 599133 * 2
def baseEnd_599133 : Nat := 273460626640275220517461

theorem tailTrace_599133 : CollatzResearch.WordTrace tailWord_599133 prefixEnd_599133 273460626640275220517461 := by
  unfold tailWord_599133
  simp only [CollatzResearch.WordTrace]
  refine ⟨21852175738450939615098053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14568117158967293076732035 21852175738450939615098053)
  ·
    refine ⟨4097282950959551177830885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21852175738450939615098053 4097282950959551177830885)
    ·
      refine ⟨768240553304915845843291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4097282950959551177830885 768240553304915845843291)
      ·
        refine ⟨1152360829957373768764937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 768240553304915845843291 1152360829957373768764937)
        ·
          refine ⟨864270622468030326573703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1152360829957373768764937 864270622468030326573703)
          ·
            refine ⟨1296405933702045489860555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 864270622468030326573703 1296405933702045489860555)
            ·
              refine ⟨1944608900553068234790833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1296405933702045489860555 1944608900553068234790833)
              ·
                refine ⟨1458456675414801176093125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1944608900553068234790833 1458456675414801176093125)
                ·
                  refine ⟨273460626640275220517461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1458456675414801176093125 273460626640275220517461)
                  ·
                    rfl

theorem cell20_599133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 2, 4].length) (baseStart_599133 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_599133 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_599133 prefixEnd_599133 := by exact prefixLift 599133
  have htrace : WordTrace (prefixWord ++ tailWord_599133) baseStart_599133 baseEnd_599133 := by
    simpa [prefixWord, tailWord_599133, baseEnd_599133] using wordTrace_append hprefix tailTrace_599133
  have hstable : (prefixWord ++ tailWord_599133).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599133).length < 2 ^ (prefixWord ++ tailWord_599133).sum := by decide
  have hdescent : baseEnd_599133 < baseStart_599133 := by decide
  rcases family_descends (prefixWord ++ tailWord_599133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599151 : List Nat := [1, 1, 2, 1, 3, 3, 2, 2, 5]
def baseStart_599151 : Nat := 118140960795 + 599151 * 2 ^ 59
def prefixEnd_599151 : Nat := 4983230072969 + 3 ^ 40 * 599151 * 2
def baseEnd_599151 : Nat := 273468842330747157917387

theorem tailTrace_599151 : CollatzResearch.WordTrace tailWord_599151 prefixEnd_599151 273468842330747157917387 := by
  unfold tailWord_599151
  simp only [CollatzResearch.WordTrace]
  refine ⟨21852832252385728689253307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14568554834923819126168871 21852832252385728689253307)
  ·
    refine ⟨32779248378578593033879961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21852832252385728689253307 32779248378578593033879961)
    ·
      refine ⟨24584436283933944775409971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32779248378578593033879961 24584436283933944775409971)
      ·
        refine ⟨36876654425900917163114957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24584436283933944775409971 36876654425900917163114957)
        ·
          refine ⟨13828745409712843936168109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36876654425900917163114957 13828745409712843936168109)
          ·
            refine ⟨5185779528642316476063041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13828745409712843936168109 5185779528642316476063041)
            ·
              refine ⟨3889334646481737357047281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5185779528642316476063041 3889334646481737357047281)
              ·
                refine ⟨2917000984861303017785461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3889334646481737357047281 2917000984861303017785461)
                ·
                  refine ⟨273468842330747157917387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2917000984861303017785461 273468842330747157917387)
                  ·
                    rfl

theorem cell20_599151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 5].length) (baseStart_599151 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_599151 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_599151 prefixEnd_599151 := by exact prefixLift 599151
  have htrace : WordTrace (prefixWord ++ tailWord_599151) baseStart_599151 baseEnd_599151 := by
    simpa [prefixWord, tailWord_599151, baseEnd_599151] using wordTrace_append hprefix tailTrace_599151
  have hstable : (prefixWord ++ tailWord_599151).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599151).length < 2 ^ (prefixWord ++ tailWord_599151).sum := by decide
  have hdescent : baseEnd_599151 < baseStart_599151 := by decide
  rcases family_descends (prefixWord ++ tailWord_599151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599168 : List Nat := [2, 1, 1, 2, 1, 3, 5, 2, 3]
def baseStart_599168 : Nat := 118140960795 + 599168 * 2 ^ 59
def prefixEnd_599168 : Nat := 4983230072969 + 3 ^ 40 * 599168 * 2
def baseEnd_599168 : Nat := 273476601593970654350651

theorem tailTrace_599168 : CollatzResearch.WordTrace tailWord_599168 prefixEnd_599168 273476601593970654350651 := by
  unfold tailWord_599168
  simp only [CollatzResearch.WordTrace]
  refine ⟨10926726146662070296311079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14568968195549427061748105 10926726146662070296311079)
  ·
    refine ⟨16390089219993105444466619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10926726146662070296311079 16390089219993105444466619)
    ·
      refine ⟨24585133829989658166699929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16390089219993105444466619 24585133829989658166699929)
      ·
        refine ⟨18438850372492243625024947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24585133829989658166699929 18438850372492243625024947)
        ·
          refine ⟨27658275558738365437537421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18438850372492243625024947 27658275558738365437537421)
          ·
            refine ⟨10371853334526887039076533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27658275558738365437537421 10371853334526887039076533)
            ·
              refine ⟨972361250111895659913425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10371853334526887039076533 972361250111895659913425)
              ·
                refine ⟨729270937583921744935069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 972361250111895659913425 729270937583921744935069)
                ·
                  refine ⟨273476601593970654350651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 729270937583921744935069 273476601593970654350651)
                  ·
                    rfl

theorem cell20_599168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 2, 3].length) (baseStart_599168 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_599168 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_599168 prefixEnd_599168 := by exact prefixLift 599168
  have htrace : WordTrace (prefixWord ++ tailWord_599168) baseStart_599168 baseEnd_599168 := by
    simpa [prefixWord, tailWord_599168, baseEnd_599168] using wordTrace_append hprefix tailTrace_599168
  have hstable : (prefixWord ++ tailWord_599168).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599168).length < 2 ^ (prefixWord ++ tailWord_599168).sum := by decide
  have hdescent : baseEnd_599168 < baseStart_599168 := by decide
  rcases family_descends (prefixWord ++ tailWord_599168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599199 : List Nat := [1, 1, 2, 6, 2, 1, 1, 6]
def baseStart_599199 : Nat := 118140960795 + 599199 * 2 ^ 59
def prefixEnd_599199 : Nat := 4983230072969 + 3 ^ 40 * 599199 * 2
def baseEnd_599199 : Nat := 91163583612890774772397

theorem tailTrace_599199 : CollatzResearch.WordTrace tailWord_599199 prefixEnd_599199 91163583612890774772397 := by
  unfold tailWord_599199
  simp only [CollatzResearch.WordTrace]
  refine ⟨21854582956211832887000651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14569721970807888591333767 21854582956211832887000651)
  ·
    refine ⟨32781874434317749330500977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21854582956211832887000651 32781874434317749330500977)
    ·
      refine ⟨24586405825738311997875733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32781874434317749330500977 24586405825738311997875733)
      ·
        refine ⟨1152487773081483374900425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 24586405825738311997875733 1152487773081483374900425)
        ·
          refine ⟨864365829811112531175319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1152487773081483374900425 864365829811112531175319)
          ·
            refine ⟨1296548744716668796762979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 864365829811112531175319 1296548744716668796762979)
            ·
              refine ⟨1944823117075003195144469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1296548744716668796762979 1944823117075003195144469)
              ·
                refine ⟨91163583612890774772397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1944823117075003195144469 91163583612890774772397)
                ·
                  rfl

theorem cell20_599199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 6].length) (baseStart_599199 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_599199 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_599199 prefixEnd_599199 := by exact prefixLift 599199
  have htrace : WordTrace (prefixWord ++ tailWord_599199) baseStart_599199 baseEnd_599199 := by
    simpa [prefixWord, tailWord_599199, baseEnd_599199] using wordTrace_append hprefix tailTrace_599199
  have hstable : (prefixWord ++ tailWord_599199).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599199).length < 2 ^ (prefixWord ++ tailWord_599199).sum := by decide
  have hdescent : baseEnd_599199 < baseStart_599199 := by decide
  rcases family_descends (prefixWord ++ tailWord_599199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599222 : List Nat := [5, 1, 3, 2, 1, 1, 3, 2, 2]
def baseStart_599222 : Nat := 118140960795 + 599222 * 2 ^ 59
def prefixEnd_599222 : Nat := 4983230072969 + 3 ^ 40 * 599222 * 2
def baseEnd_599222 : Nat := 273501248665386466550431

theorem tailTrace_599222 : CollatzResearch.WordTrace tailWord_599222 prefixEnd_599222 273501248665386466550431 := by
  unfold tailWord_599222
  simp only [CollatzResearch.WordTrace]
  refine ⟨1365963864695531738442995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14570281223419005210058613 1365963864695531738442995)
  ·
    refine ⟨2048945797043297607664493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1365963864695531738442995 2048945797043297607664493)
    ·
      refine ⟨768354673891236602874185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2048945797043297607664493 768354673891236602874185)
      ·
        refine ⟨576266005418427452155639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 768354673891236602874185 576266005418427452155639)
        ·
          refine ⟨864399008127641178233459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 576266005418427452155639 864399008127641178233459)
          ·
            refine ⟨1296598512191461767350189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 864399008127641178233459 1296598512191461767350189)
            ·
              refine ⟨486224442071798162756321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1296598512191461767350189 486224442071798162756321)
              ·
                refine ⟨364668331553848622067241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 486224442071798162756321 364668331553848622067241)
                ·
                  refine ⟨273501248665386466550431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 364668331553848622067241 273501248665386466550431)
                  ·
                    rfl

theorem cell20_599222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 3, 2, 2].length) (baseStart_599222 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_599222 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_599222 prefixEnd_599222 := by exact prefixLift 599222
  have htrace : WordTrace (prefixWord ++ tailWord_599222) baseStart_599222 baseEnd_599222 := by
    simpa [prefixWord, tailWord_599222, baseEnd_599222] using wordTrace_append hprefix tailTrace_599222
  have hstable : (prefixWord ++ tailWord_599222).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599222).length < 2 ^ (prefixWord ++ tailWord_599222).sum := by decide
  have hdescent : baseEnd_599222 < baseStart_599222 := by decide
  rcases family_descends (prefixWord ++ tailWord_599222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599230 : List Nat := [4, 2, 1, 1, 3, 1, 3, 1, 4]
def baseStart_599230 : Nat := 118140960795 + 599230 * 2 ^ 59
def prefixEnd_599230 : Nat := 4983230072969 + 3 ^ 40 * 599230 * 2
def baseEnd_599230 : Nat := 273504900083373994283731

theorem tailTrace_599230 : CollatzResearch.WordTrace tailWord_599230 prefixEnd_599230 273504900083373994283731 := by
  unfold tailWord_599230
  simp only [CollatzResearch.WordTrace]
  refine ⟨2731964202387440647672393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14570475746066350120919429 2731964202387440647672393)
  ·
    refine ⟨2048973151790580485754295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2731964202387440647672393 2048973151790580485754295)
    ·
      refine ⟨3073459727685870728631443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2048973151790580485754295 3073459727685870728631443)
      ·
        refine ⟨4610189591528806092947165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3073459727685870728631443 4610189591528806092947165)
        ·
          refine ⟨1728821096823302284855187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4610189591528806092947165 1728821096823302284855187)
          ·
            refine ⟨2593231645234953427282781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1728821096823302284855187 2593231645234953427282781)
            ·
              refine ⟨972461866963107535231043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2593231645234953427282781 972461866963107535231043)
              ·
                refine ⟨1458692800444661302846565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 972461866963107535231043 1458692800444661302846565)
                ·
                  refine ⟨273504900083373994283731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1458692800444661302846565 273504900083373994283731)
                  ·
                    rfl

theorem cell20_599230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_599230 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_599230 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_599230 prefixEnd_599230 := by exact prefixLift 599230
  have htrace : WordTrace (prefixWord ++ tailWord_599230) baseStart_599230 baseEnd_599230 := by
    simpa [prefixWord, tailWord_599230, baseEnd_599230] using wordTrace_append hprefix tailTrace_599230
  have hstable : (prefixWord ++ tailWord_599230).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599230).length < 2 ^ (prefixWord ++ tailWord_599230).sum := by decide
  have hdescent : baseEnd_599230 < baseStart_599230 := by decide
  rcases family_descends (prefixWord ++ tailWord_599230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599279 : List Nat := [1, 1, 2, 1, 15]
def baseStart_599279 : Nat := 118140960795 + 599279 * 2 ^ 59
def prefixEnd_599279 : Nat := 4983230072969 + 3 ^ 40 * 599279 * 2
def baseEnd_599279 : Nat := 3376879815043797551237

theorem tailTrace_599279 : CollatzResearch.WordTrace tailWord_599279 prefixEnd_599279 3376879815043797551237 := by
  unfold tailWord_599279
  simp only [CollatzResearch.WordTrace]
  refine ⟨21857500795922006549912891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14571667197281337699941927 21857500795922006549912891)
  ·
    refine ⟨32786251193883009824869337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21857500795922006549912891 32786251193883009824869337)
    ·
      refine ⟨24589688395412257368652003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32786251193883009824869337 24589688395412257368652003)
      ·
        refine ⟨36884532593118386052978005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24589688395412257368652003 36884532593118386052978005)
        ·
          refine ⟨3376879815043797551237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 36884532593118386052978005 3376879815043797551237)
          ·
            rfl

theorem cell20_599279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 15].length) (baseStart_599279 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_599279 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_599279 prefixEnd_599279 := by exact prefixLift 599279
  have htrace : WordTrace (prefixWord ++ tailWord_599279) baseStart_599279 baseEnd_599279 := by
    simpa [prefixWord, tailWord_599279, baseEnd_599279] using wordTrace_append hprefix tailTrace_599279
  have hstable : (prefixWord ++ tailWord_599279).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599279).length < 2 ^ (prefixWord ++ tailWord_599279).sum := by decide
  have hdescent : baseEnd_599279 < baseStart_599279 := by decide
  rcases family_descends (prefixWord ++ tailWord_599279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599292 : List Nat := [2, 2, 2, 1, 6, 1, 1, 5]
def baseStart_599292 : Nat := 118140960795 + 599292 * 2 ^ 59
def prefixEnd_599292 : Nat := 4983230072969 + 3 ^ 40 * 599292 * 2
def baseEnd_599292 : Nat := 91177732857592444738937

theorem tailTrace_599292 : CollatzResearch.WordTrace tailWord_599292 prefixEnd_599292 91177732857592444738937 := by
  unfold tailWord_599292
  simp only [CollatzResearch.WordTrace]
  refine ⟨10928987472437454885068065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14571983296583273180090753 10928987472437454885068065)
  ·
    refine ⟨8196740604328091163801049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10928987472437454885068065 8196740604328091163801049)
    ·
      refine ⟨6147555453246068372850787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8196740604328091163801049 6147555453246068372850787)
      ·
        refine ⟨9221333179869102559276181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6147555453246068372850787 9221333179869102559276181)
        ·
          refine ⟨432249992806364182466071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 9221333179869102559276181 432249992806364182466071)
          ·
            refine ⟨648374989209546273699107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 432249992806364182466071 648374989209546273699107)
            ·
              refine ⟨972562483814319410548661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 648374989209546273699107 972562483814319410548661)
              ·
                refine ⟨91177732857592444738937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 972562483814319410548661 91177732857592444738937)
                ·
                  rfl

theorem cell20_599292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 5].length) (baseStart_599292 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_599292 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_599292 prefixEnd_599292 := by exact prefixLift 599292
  have htrace : WordTrace (prefixWord ++ tailWord_599292) baseStart_599292 baseEnd_599292 := by
    simpa [prefixWord, tailWord_599292, baseEnd_599292] using wordTrace_append hprefix tailTrace_599292
  have hstable : (prefixWord ++ tailWord_599292).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599292).length < 2 ^ (prefixWord ++ tailWord_599292).sum := by decide
  have hdescent : baseEnd_599292 < baseStart_599292 := by decide
  rcases family_descends (prefixWord ++ tailWord_599292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599372 : List Nat := [2, 2, 1, 3, 2, 3, 1, 6]
def baseStart_599372 : Nat := 118140960795 + 599372 * 2 ^ 59
def prefixEnd_599372 : Nat := 4983230072969 + 3 ^ 40 * 599372 * 2
def baseEnd_599372 : Nat := 91189904250884203849939

theorem tailTrace_599372 : CollatzResearch.WordTrace tailWord_599372 prefixEnd_599372 91189904250884203849939 := by
  unfold tailWord_599372
  simp only [CollatzResearch.WordTrace]
  refine ⟨10930446392292541716524185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14573928523056722288698913 10930446392292541716524185)
  ·
    refine ⟨8197834794219406287393139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10930446392292541716524185 8197834794219406287393139)
    ·
      refine ⟨12296752191329109431089709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8197834794219406287393139 12296752191329109431089709)
      ·
        refine ⟨4611282071748416036658641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12296752191329109431089709 4611282071748416036658641)
        ·
          refine ⟨3458461553811312027493981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4611282071748416036658641 3458461553811312027493981)
          ·
            refine ⟨1296923082679242010310243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3458461553811312027493981 1296923082679242010310243)
            ·
              refine ⟨1945384624018863015465365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1296923082679242010310243 1945384624018863015465365)
              ·
                refine ⟨91189904250884203849939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1945384624018863015465365 91189904250884203849939)
                ·
                  rfl

theorem cell20_599372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 6].length) (baseStart_599372 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_599372 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_599372 prefixEnd_599372 := by exact prefixLift 599372
  have htrace : WordTrace (prefixWord ++ tailWord_599372) baseStart_599372 baseEnd_599372 := by
    simpa [prefixWord, tailWord_599372, baseEnd_599372] using wordTrace_append hprefix tailTrace_599372
  have hstable : (prefixWord ++ tailWord_599372).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599372).length < 2 ^ (prefixWord ++ tailWord_599372).sum := by decide
  have hdescent : baseEnd_599372 < baseStart_599372 := by decide
  rcases family_descends (prefixWord ++ tailWord_599372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599386 : List Nat := [3, 1, 1, 2, 1, 2, 2, 2, 6]
def baseStart_599386 : Nat := 118140960795 + 599386 * 2 ^ 59
def prefixEnd_599386 : Nat := 4983230072969 + 3 ^ 40 * 599386 * 2
def baseEnd_599386 : Nat := 273576102734130785083093

theorem tailTrace_599386 : CollatzResearch.WordTrace tailWord_599386 prefixEnd_599386 273576102734130785083093 := by
  unfold tailWord_599386
  simp only [CollatzResearch.WordTrace]
  refine ⟨5465350851633590956014503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14574268937689575882705341 5465350851633590956014503)
  ·
    refine ⟨8198026277450386434021755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5465350851633590956014503 8198026277450386434021755)
    ·
      refine ⟨12297039416175579651032633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8198026277450386434021755 12297039416175579651032633)
      ·
        refine ⟨9222779562131684738274475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12297039416175579651032633 9222779562131684738274475)
        ·
          refine ⟨13834169343197527107411713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9222779562131684738274475 13834169343197527107411713)
          ·
            refine ⟨10375627007398145330558785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13834169343197527107411713 10375627007398145330558785)
            ·
              refine ⟨7781720255548608997919089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10375627007398145330558785 7781720255548608997919089)
              ·
                refine ⟨5836290191661456748439317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7781720255548608997919089 5836290191661456748439317)
                ·
                  refine ⟨273576102734130785083093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5836290191661456748439317 273576102734130785083093)
                  ·
                    rfl

theorem cell20_599386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_599386 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_599386 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_599386 prefixEnd_599386 := by exact prefixLift 599386
  have htrace : WordTrace (prefixWord ++ tailWord_599386) baseStart_599386 baseEnd_599386 := by
    simpa [prefixWord, tailWord_599386, baseEnd_599386] using wordTrace_append hprefix tailTrace_599386
  have hstable : (prefixWord ++ tailWord_599386).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599386).length < 2 ^ (prefixWord ++ tailWord_599386).sum := by decide
  have hdescent : baseEnd_599386 < baseStart_599386 := by decide
  rcases family_descends (prefixWord ++ tailWord_599386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599399 : List Nat := [1, 1, 5, 1, 5, 1, 1, 1, 4]
def baseStart_599399 : Nat := 118140960795 + 599399 * 2 ^ 59
def prefixEnd_599399 : Nat := 4983230072969 + 3 ^ 40 * 599399 * 2
def baseEnd_599399 : Nat := 273582036288360517649707

theorem tailTrace_599399 : CollatzResearch.WordTrace tailWord_599399 prefixEnd_599399 273582036288360517649707 := by
  unfold tailWord_599399
  simp only [CollatzResearch.WordTrace]
  refine ⟨21861877555487267044281251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14574585036991511362854167 21861877555487267044281251)
  ·
    refine ⟨32792816333230900566421877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21861877555487267044281251 32792816333230900566421877)
    ·
      refine ⟨3074326531240396928102051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32792816333230900566421877 3074326531240396928102051)
      ·
        refine ⟨4611489796860595392153077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3074326531240396928102051 4611489796860595392153077)
        ·
          refine ⟨432327168455680818014351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4611489796860595392153077 432327168455680818014351)
          ·
            refine ⟨648490752683521227021527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 432327168455680818014351 648490752683521227021527)
            ·
              refine ⟨972736129025281840532291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 648490752683521227021527 972736129025281840532291)
              ·
                refine ⟨1459104193537922760798437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 972736129025281840532291 1459104193537922760798437)
                ·
                  refine ⟨273582036288360517649707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1459104193537922760798437 273582036288360517649707)
                  ·
                    rfl

theorem cell20_599399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 1, 4].length) (baseStart_599399 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_599399 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_599399 prefixEnd_599399 := by exact prefixLift 599399
  have htrace : WordTrace (prefixWord ++ tailWord_599399) baseStart_599399 baseEnd_599399 := by
    simpa [prefixWord, tailWord_599399, baseEnd_599399] using wordTrace_append hprefix tailTrace_599399
  have hstable : (prefixWord ++ tailWord_599399).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599399).length < 2 ^ (prefixWord ++ tailWord_599399).sum := by decide
  have hdescent : baseEnd_599399 < baseStart_599399 := by decide
  rcases family_descends (prefixWord ++ tailWord_599399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599406 : List Nat := [4, 1, 2, 4, 1, 1, 2, 5]
def baseStart_599406 : Nat := 118140960795 + 599406 * 2 ^ 59
def prefixEnd_599406 : Nat := 4983230072969 + 3 ^ 40 * 599406 * 2
def baseEnd_599406 : Nat := 91195077093033201472115

theorem tailTrace_599406 : CollatzResearch.WordTrace tailWord_599406 prefixEnd_599406 91195077093033201472115 := by
  unfold tailWord_599406
  simp only [CollatzResearch.WordTrace]
  refine ⟨2732766608307738404973259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14574755244307938159857381 2732766608307738404973259)
  ·
    refine ⟨4099149912461607607459889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2732766608307738404973259 4099149912461607607459889)
    ·
      refine ⟨3074362434346205705594917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4099149912461607607459889 3074362434346205705594917)
      ·
        refine ⟨576442956439913569799047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3074362434346205705594917 576442956439913569799047)
        ·
          refine ⟨864664434659870354698571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 576442956439913569799047 864664434659870354698571)
          ·
            refine ⟨1296996651989805532047857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 864664434659870354698571 1296996651989805532047857)
            ·
              refine ⟨972747488992354149035893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1296996651989805532047857 972747488992354149035893)
              ·
                refine ⟨91195077093033201472115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 972747488992354149035893 91195077093033201472115)
                ·
                  rfl

theorem cell20_599406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 5].length) (baseStart_599406 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_599406 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_599406 prefixEnd_599406 := by exact prefixLift 599406
  have htrace : WordTrace (prefixWord ++ tailWord_599406) baseStart_599406 baseEnd_599406 := by
    simpa [prefixWord, tailWord_599406, baseEnd_599406] using wordTrace_append hprefix tailTrace_599406
  have hstable : (prefixWord ++ tailWord_599406).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599406).length < 2 ^ (prefixWord ++ tailWord_599406).sum := by decide
  have hdescent : baseEnd_599406 < baseStart_599406 := by decide
  rcases family_descends (prefixWord ++ tailWord_599406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599410 : List Nat := [3, 2, 1, 2, 1, 2, 4, 5]
def baseStart_599410 : Nat := 118140960795 + 599410 * 2 ^ 59
def prefixEnd_599410 : Nat := 4983230072969 + 3 ^ 40 * 599410 * 2
def baseEnd_599410 : Nat := 91195685662697789427665

theorem tailTrace_599410 : CollatzResearch.WordTrace tailWord_599410 prefixEnd_599410 91195685662697789427665 := by
  unfold tailWord_599410
  simp only [CollatzResearch.WordTrace]
  refine ⟨5465569689611853980732921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14574852505631610615287789 5465569689611853980732921)
  ·
    refine ⟨4099177267208890485549691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5465569689611853980732921 4099177267208890485549691)
    ·
      refine ⟨6148765900813335728324537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4099177267208890485549691 6148765900813335728324537)
      ·
        refine ⟨4611574425610001796243403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6148765900813335728324537 4611574425610001796243403)
        ·
          refine ⟨6917361638415002694365105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4611574425610001796243403 6917361638415002694365105)
          ·
            refine ⟨5188021228811252020773829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6917361638415002694365105 5188021228811252020773829)
            ·
              refine ⟨972753980402109753895093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5188021228811252020773829 972753980402109753895093)
              ·
                refine ⟨91195685662697789427665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 972753980402109753895093 91195685662697789427665)
                ·
                  rfl

theorem cell20_599410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 5].length) (baseStart_599410 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_599410 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_599410 prefixEnd_599410 := by exact prefixLift 599410
  have htrace : WordTrace (prefixWord ++ tailWord_599410) baseStart_599410 baseEnd_599410 := by
    simpa [prefixWord, tailWord_599410, baseEnd_599410] using wordTrace_append hprefix tailTrace_599410
  have hstable : (prefixWord ++ tailWord_599410).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599410).length < 2 ^ (prefixWord ++ tailWord_599410).sum := by decide
  have hdescent : baseEnd_599410 < baseStart_599410 := by decide
  rcases family_descends (prefixWord ++ tailWord_599410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599413 : List Nat := [1, 3, 4, 1, 3, 1, 1, 3, 3]
def baseStart_599413 : Nat := 118140960795 + 599413 * 2 ^ 59
def prefixEnd_599413 : Nat := 4983230072969 + 3 ^ 40 * 599413 * 2
def baseEnd_599413 : Nat := 273588426269838691182983

theorem tailTrace_599413 : CollatzResearch.WordTrace tailWord_599413 prefixEnd_599413 273588426269838691182983 := by
  unfold tailWord_599413
  simp only [CollatzResearch.WordTrace]
  refine ⟨21862388177436547435290893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14574925451624364956860595 21862388177436547435290893)
  ·
    refine ⟨8198395566538705288234085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21862388177436547435290893 8198395566538705288234085)
    ·
      refine ⟨1537199168726007241543891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8198395566538705288234085 1537199168726007241543891)
      ·
        refine ⟨2305798753089010862315837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1537199168726007241543891 2305798753089010862315837)
        ·
          refine ⟨864674532408379073368439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2305798753089010862315837 864674532408379073368439)
          ·
            refine ⟨1297011798612568610052659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 864674532408379073368439 1297011798612568610052659)
            ·
              refine ⟨1945517697918852915078989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1297011798612568610052659 1945517697918852915078989)
              ·
                refine ⟨729569136719569843154621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1945517697918852915078989 729569136719569843154621)
                ·
                  refine ⟨273588426269838691182983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 729569136719569843154621 273588426269838691182983)
                  ·
                    rfl

theorem cell20_599413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 3, 3].length) (baseStart_599413 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_599413 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_599413 prefixEnd_599413 := by exact prefixLift 599413
  have htrace : WordTrace (prefixWord ++ tailWord_599413) baseStart_599413 baseEnd_599413 := by
    simpa [prefixWord, tailWord_599413, baseEnd_599413] using wordTrace_append hprefix tailTrace_599413
  have hstable : (prefixWord ++ tailWord_599413).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599413).length < 2 ^ (prefixWord ++ tailWord_599413).sum := by decide
  have hdescent : baseEnd_599413 < baseStart_599413 := by decide
  rcases family_descends (prefixWord ++ tailWord_599413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599424 : List Nat := [2, 1, 1, 2, 1, 2, 1, 6, 4]
def baseStart_599424 : Nat := 118140960795 + 599424 * 2 ^ 59
def prefixEnd_599424 : Nat := 4983230072969 + 3 ^ 40 * 599424 * 2
def baseEnd_599424 : Nat := 273593446969571541816271

theorem tailTrace_599424 : CollatzResearch.WordTrace tailWord_599424 prefixEnd_599424 273593446969571541816271 := by
  unfold tailWord_599424
  simp only [CollatzResearch.WordTrace]
  refine ⟨10931394690198348156970663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14575192920264464209294217 10931394690198348156970663)
  ·
    refine ⟨16397092035297522235455995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10931394690198348156970663 16397092035297522235455995)
    ·
      refine ⟨24595638052946283353183993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16397092035297522235455995 24595638052946283353183993)
      ·
        refine ⟨18446728539709712514887995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24595638052946283353183993 18446728539709712514887995)
        ·
          refine ⟨27670092809564568772331993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18446728539709712514887995 27670092809564568772331993)
          ·
            refine ⟨20752569607173426579248995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27670092809564568772331993 20752569607173426579248995)
            ·
              refine ⟨31128854410760139868873493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20752569607173426579248995 31128854410760139868873493)
              ·
                refine ⟨1459165050504381556353445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31128854410760139868873493 1459165050504381556353445)
                ·
                  refine ⟨273593446969571541816271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1459165050504381556353445 273593446969571541816271)
                  ·
                    rfl

theorem cell20_599424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 6, 4].length) (baseStart_599424 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_599424 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_599424 prefixEnd_599424 := by exact prefixLift 599424
  have htrace : WordTrace (prefixWord ++ tailWord_599424) baseStart_599424 baseEnd_599424 := by
    simpa [prefixWord, tailWord_599424, baseEnd_599424] using wordTrace_append hprefix tailTrace_599424
  have hstable : (prefixWord ++ tailWord_599424).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599424).length < 2 ^ (prefixWord ++ tailWord_599424).sum := by decide
  have hdescent : baseEnd_599424 < baseStart_599424 := by decide
  rcases family_descends (prefixWord ++ tailWord_599424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599448 : List Nat := [2, 1, 2, 5, 2, 8]
def baseStart_599448 : Nat := 118140960795 + 599448 * 2 ^ 59
def prefixEnd_599448 : Nat := 4983230072969 + 3 ^ 40 * 599448 * 2
def baseEnd_599448 : Nat := 10133496341612375000599

theorem tailTrace_599448 : CollatzResearch.WordTrace tailWord_599448 prefixEnd_599448 10133496341612375000599 := by
  unfold tailWord_599448
  simp only [CollatzResearch.WordTrace]
  refine ⟨10931832366154874206407499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14575776488206498941876665 10931832366154874206407499)
  ·
    refine ⟨16397748549232311309611249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10931832366154874206407499 16397748549232311309611249)
    ·
      refine ⟨12298311411924233482208437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16397748549232311309611249 12298311411924233482208437)
      ·
        refine ⟨1152966694867896888957041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12298311411924233482208437 1152966694867896888957041)
        ·
          refine ⟨864725021150922666717781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1152966694867896888957041 864725021150922666717781)
          ·
            refine ⟨10133496341612375000599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 864725021150922666717781 10133496341612375000599)
            ·
              rfl

theorem cell20_599448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 8].length) (baseStart_599448 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_599448 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_599448 prefixEnd_599448 := by exact prefixLift 599448
  have htrace : WordTrace (prefixWord ++ tailWord_599448) baseStart_599448 baseEnd_599448 := by
    simpa [prefixWord, tailWord_599448, baseEnd_599448] using wordTrace_append hprefix tailTrace_599448
  have hstable : (prefixWord ++ tailWord_599448).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599448).length < 2 ^ (prefixWord ++ tailWord_599448).sum := by decide
  have hdescent : baseEnd_599448 < baseStart_599448 := by decide
  rcases family_descends (prefixWord ++ tailWord_599448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599454 : List Nat := [4, 3, 1, 2, 2, 1, 1, 4, 2]
def baseStart_599454 : Nat := 118140960795 + 599454 * 2 ^ 59
def prefixEnd_599454 : Nat := 4983230072969 + 3 ^ 40 * 599454 * 2
def baseEnd_599454 : Nat := 273607139787024770816149

theorem tailTrace_599454 : CollatzResearch.WordTrace tailWord_599454 prefixEnd_599454 273607139787024770816149 := by
  unfold tailWord_599454
  simp only [CollatzResearch.WordTrace]
  refine ⟨2732985446286001429691677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14575922380192007625022277 2732985446286001429691677)
  ·
    refine ⟨1024869542357250536134379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2732985446286001429691677 1024869542357250536134379)
    ·
      refine ⟨1537304313535875804201569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1024869542357250536134379 1537304313535875804201569)
      ·
        refine ⟨1152978235151906853151177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1537304313535875804201569 1152978235151906853151177)
        ·
          refine ⟨864733676363930139863383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1152978235151906853151177 864733676363930139863383)
          ·
            refine ⟨1297100514545895209795075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 864733676363930139863383 1297100514545895209795075)
            ·
              refine ⟨1945650771818842814692613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1297100514545895209795075 1945650771818842814692613)
              ·
                refine ⟨364809519716033027754865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1945650771818842814692613 364809519716033027754865)
                ·
                  refine ⟨273607139787024770816149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 364809519716033027754865 273607139787024770816149)
                  ·
                    rfl

theorem cell20_599454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_599454 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_599454 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_599454 prefixEnd_599454 := by exact prefixLift 599454
  have htrace : WordTrace (prefixWord ++ tailWord_599454) baseStart_599454 baseEnd_599454 := by
    simpa [prefixWord, tailWord_599454, baseEnd_599454] using wordTrace_append hprefix tailTrace_599454
  have hstable : (prefixWord ++ tailWord_599454).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599454).length < 2 ^ (prefixWord ++ tailWord_599454).sum := by decide
  have hdescent : baseEnd_599454 < baseStart_599454 := by decide
  rcases family_descends (prefixWord ++ tailWord_599454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599496 : List Nat := [2, 1, 3, 1, 3, 1, 4, 3, 2]
def baseStart_599496 : Nat := 118140960795 + 599496 * 2 ^ 59
def prefixEnd_599496 : Nat := 4983230072969 + 3 ^ 40 * 599496 * 2
def baseEnd_599496 : Nat := 273626309731459291415977

theorem tailTrace_599496 : CollatzResearch.WordTrace tailWord_599496 prefixEnd_599496 273626309731459291415977 := by
  unfold tailWord_599496
  simp only [CollatzResearch.WordTrace]
  refine ⟨10932707718067926305281171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14576943624090568407041561 10932707718067926305281171)
  ·
    refine ⟨16399061577101889457921757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10932707718067926305281171 16399061577101889457921757)
    ·
      refine ⟨6149648091413208546720659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16399061577101889457921757 6149648091413208546720659)
      ·
        refine ⟨9224472137119812820080989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6149648091413208546720659 9224472137119812820080989)
        ·
          refine ⟨3459177051419929807530371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9224472137119812820080989 3459177051419929807530371)
          ·
            refine ⟨5188765577129894711295557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3459177051419929807530371 5188765577129894711295557)
            ·
              refine ⟨972893545711855258367917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5188765577129894711295557 972893545711855258367917)
              ·
                refine ⟨364835079641945721887969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 972893545711855258367917 364835079641945721887969)
                ·
                  refine ⟨273626309731459291415977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 364835079641945721887969 273626309731459291415977)
                  ·
                    rfl

theorem cell20_599496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 3, 2].length) (baseStart_599496 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_599496 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_599496 prefixEnd_599496 := by exact prefixLift 599496
  have htrace : WordTrace (prefixWord ++ tailWord_599496) baseStart_599496 baseEnd_599496 := by
    simpa [prefixWord, tailWord_599496, baseEnd_599496] using wordTrace_append hprefix tailTrace_599496
  have hstable : (prefixWord ++ tailWord_599496).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599496).length < 2 ^ (prefixWord ++ tailWord_599496).sum := by decide
  have hdescent : baseEnd_599496 < baseStart_599496 := by decide
  rcases family_descends (prefixWord ++ tailWord_599496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599517 : List Nat := [1, 4, 3, 1, 1, 2, 1, 3, 4]
def baseStart_599517 : Nat := 118140960795 + 599517 * 2 ^ 59
def prefixEnd_599517 : Nat := 4983230072969 + 3 ^ 40 * 599517 * 2
def baseEnd_599517 : Nat := 273635894703676551715891

theorem tailTrace_599517 : CollatzResearch.WordTrace tailWord_599517 prefixEnd_599517 273635894703676551715891 := by
  unfold tailWord_599517
  simp only [CollatzResearch.WordTrace]
  refine ⟨21866181369059773197076805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14577454246039848798051203 21866181369059773197076805)
  ·
    refine ⟨4099909006698707474451901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21866181369059773197076805 4099909006698707474451901)
    ·
      refine ⟨1537465877512015302919463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4099909006698707474451901 1537465877512015302919463)
      ·
        refine ⟨2306198816268022954379195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1537465877512015302919463 2306198816268022954379195)
        ·
          refine ⟨3459298224402034431568793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2306198816268022954379195 3459298224402034431568793)
          ·
            refine ⟨2594473668301525823676595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3459298224402034431568793 2594473668301525823676595)
            ·
              refine ⟨3891710502452288735514893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2594473668301525823676595 3891710502452288735514893)
              ·
                refine ⟨1459391438419608275818085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3891710502452288735514893 1459391438419608275818085)
                ·
                  refine ⟨273635894703676551715891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1459391438419608275818085 273635894703676551715891)
                  ·
                    rfl

theorem cell20_599517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_599517 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_599517 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_599517 prefixEnd_599517 := by exact prefixLift 599517
  have htrace : WordTrace (prefixWord ++ tailWord_599517) baseStart_599517 baseEnd_599517 := by
    simpa [prefixWord, tailWord_599517, baseEnd_599517] using wordTrace_append hprefix tailTrace_599517
  have hstable : (prefixWord ++ tailWord_599517).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599517).length < 2 ^ (prefixWord ++ tailWord_599517).sum := by decide
  have hdescent : baseEnd_599517 < baseStart_599517 := by decide
  rcases family_descends (prefixWord ++ tailWord_599517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599527 : List Nat := [1, 1, 5, 2, 1, 3, 3, 1, 3]
def baseStart_599527 : Nat := 118140960795 + 599527 * 2 ^ 59
def prefixEnd_599527 : Nat := 4983230072969 + 3 ^ 40 * 599527 * 2
def baseEnd_599527 : Nat := 273640458976160961382517

theorem tailTrace_599527 : CollatzResearch.WordTrace tailWord_599527 prefixEnd_599527 273640458976160961382517 := by
  unfold tailWord_599527
  simp only [CollatzResearch.WordTrace]
  refine ⟨21866546099023544904940835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14577697399349029936627223 21866546099023544904940835)
  ·
    refine ⟨32799819148535317357411253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21866546099023544904940835 32799819148535317357411253)
    ·
      refine ⟨3074983045175186002257305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32799819148535317357411253 3074983045175186002257305)
      ·
        refine ⟨2306237283881389501692979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3074983045175186002257305 2306237283881389501692979)
        ·
          refine ⟨3459355925822084252539469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2306237283881389501692979 3459355925822084252539469)
          ·
            refine ⟨1297258472183281594702301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3459355925822084252539469 1297258472183281594702301)
            ·
              refine ⟨486471927068730598013363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1297258472183281594702301 486471927068730598013363)
              ·
                refine ⟨729707890603095897020045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 486471927068730598013363 729707890603095897020045)
                ·
                  refine ⟨273640458976160961382517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 729707890603095897020045 273640458976160961382517)
                  ·
                    rfl

theorem cell20_599527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 3, 1, 3].length) (baseStart_599527 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_599527 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_599527 prefixEnd_599527 := by exact prefixLift 599527
  have htrace : WordTrace (prefixWord ++ tailWord_599527) baseStart_599527 baseEnd_599527 := by
    simpa [prefixWord, tailWord_599527, baseEnd_599527] using wordTrace_append hprefix tailTrace_599527
  have hstable : (prefixWord ++ tailWord_599527).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599527).length < 2 ^ (prefixWord ++ tailWord_599527).sum := by decide
  have hdescent : baseEnd_599527 < baseStart_599527 := by decide
  rcases family_descends (prefixWord ++ tailWord_599527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599541 : List Nat := [1, 3, 5, 1, 1, 2, 1, 6]
def baseStart_599541 : Nat := 118140960795 + 599541 * 2 ^ 59
def prefixEnd_599541 : Nat := 4983230072969 + 3 ^ 40 * 599541 * 2
def baseEnd_599541 : Nat := 91215616319213044971931

theorem tailTrace_599541 : CollatzResearch.WordTrace tailWord_599541 prefixEnd_599541 91215616319213044971931 := by
  unfold tailWord_599541
  simp only [CollatzResearch.WordTrace]
  refine ⟨21867056720972825295950477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14578037813981883530633651 21867056720972825295950477)
  ·
    refine ⟨8200146270364809485981429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21867056720972825295950477 8200146270364809485981429)
    ·
      refine ⟨768763712846700889310759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8200146270364809485981429 768763712846700889310759)
      ·
        refine ⟨1153145569270051333966139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 768763712846700889310759 1153145569270051333966139)
        ·
          refine ⟨1729718353905077000949209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1153145569270051333966139 1729718353905077000949209)
          ·
            refine ⟨1297288765428807750711907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1729718353905077000949209 1297288765428807750711907)
            ·
              refine ⟨1945933148143211626067861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1297288765428807750711907 1945933148143211626067861)
              ·
                refine ⟨91215616319213044971931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1945933148143211626067861 91215616319213044971931)
                ·
                  rfl

theorem cell20_599541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 6].length) (baseStart_599541 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_599541 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_599541 prefixEnd_599541 := by exact prefixLift 599541
  have htrace : WordTrace (prefixWord ++ tailWord_599541) baseStart_599541 baseEnd_599541 := by
    simpa [prefixWord, tailWord_599541, baseEnd_599541] using wordTrace_append hprefix tailTrace_599541
  have hstable : (prefixWord ++ tailWord_599541).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599541).length < 2 ^ (prefixWord ++ tailWord_599541).sum := by decide
  have hdescent : baseEnd_599541 < baseStart_599541 := by decide
  rcases family_descends (prefixWord ++ tailWord_599541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599555 : List Nat := [1, 1, 1, 3, 2, 1, 2, 7, 2]
def baseStart_599555 : Nat := 118140960795 + 599555 * 2 ^ 59
def prefixEnd_599555 : Nat := 4983230072969 + 3 ^ 40 * 599555 * 2
def baseEnd_599555 : Nat := 273653238939117308449069

theorem tailTrace_599555 : CollatzResearch.WordTrace tailWord_599555 prefixEnd_599555 273653238939117308449069 := by
  unfold tailWord_599555
  simp only [CollatzResearch.WordTrace]
  refine ⟨21867567342922105686960119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14578378228614737124640079 21867567342922105686960119)
  ·
    refine ⟨32801351014383158530440179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21867567342922105686960119 32801351014383158530440179)
    ·
      refine ⟨49202026521574737795660269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32801351014383158530440179 49202026521574737795660269)
      ·
        refine ⟨18450759945590526673372601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49202026521574737795660269 18450759945590526673372601)
        ·
          refine ⟨13838069959192895005029451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18450759945590526673372601 13838069959192895005029451)
          ·
            refine ⟨20757104938789342507544177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13838069959192895005029451 20757104938789342507544177)
            ·
              refine ⟨15567828704092006880658133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20757104938789342507544177 15567828704092006880658133)
              ·
                refine ⟨364870985252156411265425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 15567828704092006880658133 364870985252156411265425)
                ·
                  refine ⟨273653238939117308449069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 364870985252156411265425 273653238939117308449069)
                  ·
                    rfl

theorem cell20_599555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 7, 2].length) (baseStart_599555 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_599555 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_599555 prefixEnd_599555 := by exact prefixLift 599555
  have htrace : WordTrace (prefixWord ++ tailWord_599555) baseStart_599555 baseEnd_599555 := by
    simpa [prefixWord, tailWord_599555, baseEnd_599555] using wordTrace_append hprefix tailTrace_599555
  have hstable : (prefixWord ++ tailWord_599555).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599555).length < 2 ^ (prefixWord ++ tailWord_599555).sum := by decide
  have hdescent : baseEnd_599555 < baseStart_599555 := by decide
  rcases family_descends (prefixWord ++ tailWord_599555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599562 : List Nat := [3, 1, 2, 2, 2, 4, 6]
def baseStart_599562 : Nat := 118140960795 + 599562 * 2 ^ 59
def prefixEnd_599562 : Nat := 4983230072969 + 3 ^ 40 * 599562 * 2
def baseEnd_599562 : Nat := 30406270436650710579523

theorem tailTrace_599562 : CollatzResearch.WordTrace tailWord_599562 prefixEnd_599562 30406270436650710579523 := by
  unfold tailWord_599562
  simp only [CollatzResearch.WordTrace]
  refine ⟨5466955663474186470616235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14578548435931163921643293 5466955663474186470616235)
  ·
    refine ⟨8200433495211279705924353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5466955663474186470616235 8200433495211279705924353)
    ·
      refine ⟨6150325121408459779443265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8200433495211279705924353 6150325121408459779443265)
      ·
        refine ⟨4612743841056344834582449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6150325121408459779443265 4612743841056344834582449)
        ·
          refine ⟨3459557880792258625936837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4612743841056344834582449 3459557880792258625936837)
          ·
            refine ⟨648667102648548492363157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3459557880792258625936837 648667102648548492363157)
            ·
              refine ⟨30406270436650710579523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 648667102648548492363157 30406270436650710579523)
              ·
                rfl

theorem cell20_599562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 6].length) (baseStart_599562 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_599562 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_599562 prefixEnd_599562 := by exact prefixLift 599562
  have htrace : WordTrace (prefixWord ++ tailWord_599562) baseStart_599562 baseEnd_599562 := by
    simpa [prefixWord, tailWord_599562, baseEnd_599562] using wordTrace_append hprefix tailTrace_599562
  have hstable : (prefixWord ++ tailWord_599562).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599562).length < 2 ^ (prefixWord ++ tailWord_599562).sum := by decide
  have hdescent : baseEnd_599562 < baseStart_599562 := by decide
  rcases family_descends (prefixWord ++ tailWord_599562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599569 : List Nat := [1, 2, 2, 1, 1, 2, 4, 4, 3]
def baseStart_599569 : Nat := 118140960795 + 599569 * 2 ^ 59
def prefixEnd_599569 : Nat := 4983230072969 + 3 ^ 40 * 599569 * 2
def baseEnd_599569 : Nat := 273659628920595481982345

theorem tailTrace_599569 : CollatzResearch.WordTrace tailWord_599569 prefixEnd_599569 273659628920595481982345 := by
  unfold tailWord_599569
  simp only [CollatzResearch.WordTrace]
  refine ⟨21868077964871386077969761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14578718643247590718646507 21868077964871386077969761)
  ·
    refine ⟨16401058473653539558477321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21868077964871386077969761 16401058473653539558477321)
    ·
      refine ⟨12300793855240154668857991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16401058473653539558477321 12300793855240154668857991)
      ·
        refine ⟨18451190782860232003286987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12300793855240154668857991 18451190782860232003286987)
        ·
          refine ⟨27676786174290348004930481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18451190782860232003286987 27676786174290348004930481)
          ·
            refine ⟨20757589630717761003697861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27676786174290348004930481 20757589630717761003697861)
            ·
              refine ⟨3892048055759580188193349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20757589630717761003697861 3892048055759580188193349)
              ·
                refine ⟨729759010454921285286253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3892048055759580188193349 729759010454921285286253)
                ·
                  refine ⟨273659628920595481982345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 729759010454921285286253 273659628920595481982345)
                  ·
                    rfl

theorem cell20_599569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 4, 3].length) (baseStart_599569 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_599569 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_599569 prefixEnd_599569 := by exact prefixLift 599569
  have htrace : WordTrace (prefixWord ++ tailWord_599569) baseStart_599569 baseEnd_599569 := by
    simpa [prefixWord, tailWord_599569, baseEnd_599569] using wordTrace_append hprefix tailTrace_599569
  have hstable : (prefixWord ++ tailWord_599569).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599569).length < 2 ^ (prefixWord ++ tailWord_599569).sum := by decide
  have hdescent : baseEnd_599569 < baseStart_599569 := by decide
  rcases family_descends (prefixWord ++ tailWord_599569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599583 : List Nat := [1, 1, 2, 4, 1, 1, 3, 7]
def baseStart_599583 : Nat := 118140960795 + 599583 * 2 ^ 59
def prefixEnd_599583 : Nat := 4983230072969 + 3 ^ 40 * 599583 * 2
def baseEnd_599583 : Nat := 91222006300691218505207

theorem tailTrace_599583 : CollatzResearch.WordTrace tailWord_599583 prefixEnd_599583 91222006300691218505207 := by
  unfold tailWord_599583
  simp only [CollatzResearch.WordTrace]
  refine ⟨21868588586820666468979403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14579059057880444312652935 21868588586820666468979403)
  ·
    refine ⟨32802882880230999703469105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21868588586820666468979403 32802882880230999703469105)
    ·
      refine ⟨24602162160173249777601829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32802882880230999703469105 24602162160173249777601829)
      ·
        refine ⟨4612905405032484333300343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24602162160173249777601829 4612905405032484333300343)
        ·
          refine ⟨6919358107548726499950515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4612905405032484333300343 6919358107548726499950515)
          ·
            refine ⟨10379037161323089749925773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6919358107548726499950515 10379037161323089749925773)
            ·
              refine ⟨3892138935496158656222165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10379037161323089749925773 3892138935496158656222165)
              ·
                refine ⟨91222006300691218505207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3892138935496158656222165 91222006300691218505207)
                ·
                  rfl

theorem cell20_599583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 7].length) (baseStart_599583 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_599583 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_599583 prefixEnd_599583 := by exact prefixLift 599583
  have htrace : WordTrace (prefixWord ++ tailWord_599583) baseStart_599583 baseEnd_599583 := by
    simpa [prefixWord, tailWord_599583, baseEnd_599583] using wordTrace_append hprefix tailTrace_599583
  have hstable : (prefixWord ++ tailWord_599583).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599583).length < 2 ^ (prefixWord ++ tailWord_599583).sum := by decide
  have hdescent : baseEnd_599583 < baseStart_599583 := by decide
  rcases family_descends (prefixWord ++ tailWord_599583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599652 : List Nat := [2, 3, 1, 1, 2, 3, 1, 1, 6]
def baseStart_599652 : Nat := 118140960795 + 599652 * 2 ^ 59
def prefixEnd_599652 : Nat := 4983230072969 + 3 ^ 40 * 599652 * 2
def baseEnd_599652 : Nat := 273697512382216082215339

theorem tailTrace_599652 : CollatzResearch.WordTrace tailWord_599652 prefixEnd_599652 273697512382216082215339 := by
  unfold tailWord_599652
  simp only [CollatzResearch.WordTrace]
  refine ⟨10935552611785345626620605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14580736815713794168827473 10935552611785345626620605)
  ·
    refine ⟨4100832229419504609982727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10935552611785345626620605 4100832229419504609982727)
    ·
      refine ⟨6151248344129256914974091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4100832229419504609982727 6151248344129256914974091)
      ·
        refine ⟨9226872516193885372461137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6151248344129256914974091 9226872516193885372461137)
        ·
          refine ⟨6920154387145414029345853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9226872516193885372461137 6920154387145414029345853)
          ·
            refine ⟨2595057895179530261004695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6920154387145414029345853 2595057895179530261004695)
            ·
              refine ⟨3892586842769295391507043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2595057895179530261004695 3892586842769295391507043)
              ·
                refine ⟨5838880264153943087260565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3892586842769295391507043 5838880264153943087260565)
                ·
                  refine ⟨273697512382216082215339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5838880264153943087260565 273697512382216082215339)
                  ·
                    rfl

theorem cell20_599652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_599652 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_599652 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_599652 prefixEnd_599652 := by exact prefixLift 599652
  have htrace : WordTrace (prefixWord ++ tailWord_599652) baseStart_599652 baseEnd_599652 := by
    simpa [prefixWord, tailWord_599652, baseEnd_599652] using wordTrace_append hprefix tailTrace_599652
  have hstable : (prefixWord ++ tailWord_599652).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599652).length < 2 ^ (prefixWord ++ tailWord_599652).sum := by decide
  have hdescent : baseEnd_599652 < baseStart_599652 := by decide
  rcases family_descends (prefixWord ++ tailWord_599652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599710 : List Nat := [4, 3, 1, 1, 1, 4, 2, 4]
def baseStart_599710 : Nat := 118140960795 + 599710 * 2 ^ 59
def prefixEnd_599710 : Nat := 4983230072969 + 3 ^ 40 * 599710 * 2
def baseEnd_599710 : Nat := 91241328387541886093923

theorem tailTrace_599710 : CollatzResearch.WordTrace tailWord_599710 prefixEnd_599710 91241328387541886093923 := by
  unfold tailWord_599710
  simp only [CollatzResearch.WordTrace]
  refine ⟨2734152582170070894856573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14582147104907044772568389 2734152582170070894856573)
  ·
    refine ⟨1025307218313776585571215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2734152582170070894856573 1025307218313776585571215)
    ·
      refine ⟨1537960827470664878356823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1025307218313776585571215 1537960827470664878356823)
      ·
        refine ⟨2306941241205997317535235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1537960827470664878356823 2306941241205997317535235)
        ·
          refine ⟨3460411861808995976302853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2306941241205997317535235 3460411861808995976302853)
          ·
            refine ⟨648827224089186745556785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3460411861808995976302853 648827224089186745556785)
            ·
              refine ⟨486620418066890059167589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 648827224089186745556785 486620418066890059167589)
              ·
                refine ⟨91241328387541886093923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 486620418066890059167589 91241328387541886093923)
                ·
                  rfl

theorem cell20_599710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 2, 4].length) (baseStart_599710 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_599710 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_599710 prefixEnd_599710 := by exact prefixLift 599710
  have htrace : WordTrace (prefixWord ++ tailWord_599710) baseStart_599710 baseEnd_599710 := by
    simpa [prefixWord, tailWord_599710, baseEnd_599710] using wordTrace_append hprefix tailTrace_599710
  have hstable : (prefixWord ++ tailWord_599710).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599710).length < 2 ^ (prefixWord ++ tailWord_599710).sum := by decide
  have hdescent : baseEnd_599710 < baseStart_599710 := by decide
  rcases family_descends (prefixWord ++ tailWord_599710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599735 : List Nat := [1, 1, 3, 1, 5, 1, 8]
def baseStart_599735 : Nat := 118140960795 + 599735 * 2 ^ 59
def prefixEnd_599735 : Nat := 4983230072969 + 3 ^ 40 * 599735 * 2
def baseEnd_599735 : Nat := 30415043982648520272037

theorem tailTrace_599735 : CollatzResearch.WordTrace tailWord_599735 prefixEnd_599735 30415043982648520272037 := by
  unfold tailWord_599735
  simp only [CollatzResearch.WordTrace]
  refine ⟨21874132482269996428512659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14582754988179997619008439 21874132482269996428512659)
  ·
    refine ⟨32811198723404994642768989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21874132482269996428512659 32811198723404994642768989)
    ·
      refine ⟨12304199521276872991038371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32811198723404994642768989 12304199521276872991038371)
      ·
        refine ⟨18456299281915309486557557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12304199521276872991038371 18456299281915309486557557)
        ·
          refine ⟨1730278057679560264364771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18456299281915309486557557 1730278057679560264364771)
          ·
            refine ⟨2595417086519340396547157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1730278057679560264364771 2595417086519340396547157)
            ·
              refine ⟨30415043982648520272037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2595417086519340396547157 30415043982648520272037)
              ·
                rfl

theorem cell20_599735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 8].length) (baseStart_599735 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_599735 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_599735 prefixEnd_599735 := by exact prefixLift 599735
  have htrace : WordTrace (prefixWord ++ tailWord_599735) baseStart_599735 baseEnd_599735 := by
    simpa [prefixWord, tailWord_599735, baseEnd_599735] using wordTrace_append hprefix tailTrace_599735
  have hstable : (prefixWord ++ tailWord_599735).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599735).length < 2 ^ (prefixWord ++ tailWord_599735).sum := by decide
  have hdescent : baseEnd_599735 < baseStart_599735 := by decide
  rcases family_descends (prefixWord ++ tailWord_599735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599796 : List Nat := [2, 6, 1, 1, 1, 2, 1, 4, 2]
def baseStart_599796 : Nat := 118140960795 + 599796 * 2 ^ 59
def prefixEnd_599796 : Nat := 4983230072969 + 3 ^ 40 * 599796 * 2
def baseEnd_599796 : Nat := 273763237905991581414751

theorem tailTrace_599796 : CollatzResearch.WordTrace tailWord_599796 prefixEnd_599796 273763237905991581414751 := by
  unfold tailWord_599796
  simp only [CollatzResearch.WordTrace]
  refine ⟨10938178667524501923241621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14584238223366002564322161 10938178667524501923241621)
  ·
    refine ⟨512727125040211027651951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 10938178667524501923241621 512727125040211027651951)
    ·
      refine ⟨769090687560316541477927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 512727125040211027651951 769090687560316541477927)
      ·
        refine ⟨1153636031340474812216891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 769090687560316541477927 1153636031340474812216891)
        ·
          refine ⟨1730454047010712218325337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1153636031340474812216891 1730454047010712218325337)
          ·
            refine ⟨1297840535258034163744003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1730454047010712218325337 1297840535258034163744003)
            ·
              refine ⟨1946760802887051245616005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1297840535258034163744003 1946760802887051245616005)
              ·
                refine ⟨365017650541322108553001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1946760802887051245616005 365017650541322108553001)
                ·
                  refine ⟨273763237905991581414751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 365017650541322108553001 273763237905991581414751)
                  ·
                    rfl

theorem cell20_599796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_599796 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_599796 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_599796 prefixEnd_599796 := by exact prefixLift 599796
  have htrace : WordTrace (prefixWord ++ tailWord_599796) baseStart_599796 baseEnd_599796 := by
    simpa [prefixWord, tailWord_599796, baseEnd_599796] using wordTrace_append hprefix tailTrace_599796
  have hstable : (prefixWord ++ tailWord_599796).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599796).length < 2 ^ (prefixWord ++ tailWord_599796).sum := by decide
  have hdescent : baseEnd_599796 < baseStart_599796 := by decide
  rcases family_descends (prefixWord ++ tailWord_599796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599804 : List Nat := [2, 2, 2, 1, 3, 1, 2, 3, 4]
def baseStart_599804 : Nat := 118140960795 + 599804 * 2 ^ 59
def prefixEnd_599804 : Nat := 4983230072969 + 3 ^ 40 * 599804 * 2
def baseEnd_599804 : Nat := 273766889323979109148051

theorem tailTrace_599804 : CollatzResearch.WordTrace tailWord_599804 prefixEnd_599804 273766889323979109148051 := by
  unfold tailWord_599804
  simp only [CollatzResearch.WordTrace]
  refine ⟨10938324559510010606387233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14584432746013347475182977 10938324559510010606387233)
  ·
    refine ⟨8203743419632507954790425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10938324559510010606387233 8203743419632507954790425)
    ·
      refine ⟨6152807564724380966092819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8203743419632507954790425 6152807564724380966092819)
      ·
        refine ⟨9229211347086571449139229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6152807564724380966092819 9229211347086571449139229)
        ·
          refine ⟨3460954255157464293427211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9229211347086571449139229 3460954255157464293427211)
          ·
            refine ⟨5191431382736196440140817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3460954255157464293427211 5191431382736196440140817)
            ·
              refine ⟨3893573537052147330105613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5191431382736196440140817 3893573537052147330105613)
              ·
                refine ⟨1460090076394555248789605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3893573537052147330105613 1460090076394555248789605)
                ·
                  refine ⟨273766889323979109148051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1460090076394555248789605 273766889323979109148051)
                  ·
                    rfl

theorem cell20_599804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 3, 4].length) (baseStart_599804 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_599804 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_599804 prefixEnd_599804 := by exact prefixLift 599804
  have htrace : WordTrace (prefixWord ++ tailWord_599804) baseStart_599804 baseEnd_599804 := by
    simpa [prefixWord, tailWord_599804, baseEnd_599804] using wordTrace_append hprefix tailTrace_599804
  have hstable : (prefixWord ++ tailWord_599804).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599804).length < 2 ^ (prefixWord ++ tailWord_599804).sum := by decide
  have hdescent : baseEnd_599804 < baseStart_599804 := by decide
  rcases family_descends (prefixWord ++ tailWord_599804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599811 : List Nat := [1, 1, 1, 3, 2, 2, 5, 5]
def baseStart_599811 : Nat := 118140960795 + 599811 * 2 ^ 59
def prefixEnd_599811 : Nat := 4983230072969 + 3 ^ 40 * 599811 * 2
def baseEnd_599811 : Nat := 91256694771572731971563

theorem tailTrace_599811 : CollatzResearch.WordTrace tailWord_599811 prefixEnd_599811 91256694771572731971563 := by
  unfold tailWord_599811
  simp only [CollatzResearch.WordTrace]
  refine ⟨21876904429994661408279287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14584602953329774272186191 21876904429994661408279287)
  ·
    refine ⟨32815356644991992112418931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21876904429994661408279287 32815356644991992112418931)
    ·
      refine ⟨49223034967487988168628397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32815356644991992112418931 49223034967487988168628397)
      ·
        refine ⟨18458638112807995563235649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49223034967487988168628397 18458638112807995563235649)
        ·
          refine ⟨13843978584605996672426737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18458638112807995563235649 13843978584605996672426737)
          ·
            refine ⟨10382983938454497504320053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13843978584605996672426737 10382983938454497504320053)
            ·
              refine ⟨973404744230109141030005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10382983938454497504320053 973404744230109141030005)
              ·
                refine ⟨91256694771572731971563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 973404744230109141030005 91256694771572731971563)
                ·
                  rfl

theorem cell20_599811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 5].length) (baseStart_599811 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_599811 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_599811 prefixEnd_599811 := by exact prefixLift 599811
  have htrace : WordTrace (prefixWord ++ tailWord_599811) baseStart_599811 baseEnd_599811 := by
    simpa [prefixWord, tailWord_599811, baseEnd_599811] using wordTrace_append hprefix tailTrace_599811
  have hstable : (prefixWord ++ tailWord_599811).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599811).length < 2 ^ (prefixWord ++ tailWord_599811).sum := by decide
  have hdescent : baseEnd_599811 < baseStart_599811 := by decide
  rcases family_descends (prefixWord ++ tailWord_599811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599842 : List Nat := [3, 3, 1, 1, 2, 1, 1, 2, 6]
def baseStart_599842 : Nat := 118140960795 + 599842 * 2 ^ 59
def prefixEnd_599842 : Nat := 4983230072969 + 3 ^ 40 * 599842 * 2
def baseEnd_599842 : Nat := 273784233559419865881229

theorem tailTrace_599842 : CollatzResearch.WordTrace tailWord_599842 prefixEnd_599842 273784233559419865881229 := by
  unfold tailWord_599842
  simp only [CollatzResearch.WordTrace]
  refine ⟨5469508773220588425664445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14585356728588235801771853 5469508773220588425664445)
  ·
    refine ⟨2051065789957720659624167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5469508773220588425664445 2051065789957720659624167)
    ·
      refine ⟨3076598684936580989436251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2051065789957720659624167 3076598684936580989436251)
      ·
        refine ⟨4614898027404871484154377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3076598684936580989436251 4614898027404871484154377)
        ·
          refine ⟨3461173520553653613115783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4614898027404871484154377 3461173520553653613115783)
          ·
            refine ⟨5191760280830480419673675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3461173520553653613115783 5191760280830480419673675)
            ·
              refine ⟨7787640421245720629510513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5191760280830480419673675 7787640421245720629510513)
              ·
                refine ⟨5840730315934290472132885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7787640421245720629510513 5840730315934290472132885)
                ·
                  refine ⟨273784233559419865881229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5840730315934290472132885 273784233559419865881229)
                  ·
                    rfl

theorem cell20_599842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_599842 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_599842 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_599842 prefixEnd_599842 := by exact prefixLift 599842
  have htrace : WordTrace (prefixWord ++ tailWord_599842) baseStart_599842 baseEnd_599842 := by
    simpa [prefixWord, tailWord_599842, baseEnd_599842] using wordTrace_append hprefix tailTrace_599842
  have hstable : (prefixWord ++ tailWord_599842).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599842).length < 2 ^ (prefixWord ++ tailWord_599842).sum := by decide
  have hdescent : baseEnd_599842 < baseStart_599842 := by decide
  rcases family_descends (prefixWord ++ tailWord_599842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599852 : List Nat := [2, 2, 1, 1, 1, 7, 1, 2, 3]
def baseStart_599852 : Nat := 118140960795 + 599852 * 2 ^ 59
def prefixEnd_599852 : Nat := 4983230072969 + 3 ^ 40 * 599852 * 2
def baseEnd_599852 : Nat := 273788797831904275547855

theorem tailTrace_599852 : CollatzResearch.WordTrace tailWord_599852 prefixEnd_599852 273788797831904275547855 := by
  unfold tailWord_599852
  simp only [CollatzResearch.WordTrace]
  refine ⟨10939199911423062705260905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14585599881897416940347873 10939199911423062705260905)
  ·
    refine ⟨8204399933567297028945679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10939199911423062705260905 8204399933567297028945679)
    ·
      refine ⟨12306599900350945543418519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8204399933567297028945679 12306599900350945543418519)
      ·
        refine ⟨18459899850526418315127779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12306599900350945543418519 18459899850526418315127779)
        ·
          refine ⟨27689849775789627472691669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18459899850526418315127779 27689849775789627472691669)
          ·
            refine ⟨648980854120069393891211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 27689849775789627472691669 648980854120069393891211)
            ·
              refine ⟨973471281180104090836817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 648980854120069393891211 973471281180104090836817)
              ·
                refine ⟨730103460885078068127613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 973471281180104090836817 730103460885078068127613)
                ·
                  refine ⟨273788797831904275547855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 730103460885078068127613 273788797831904275547855)
                  ·
                    rfl

theorem cell20_599852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 3].length) (baseStart_599852 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_599852 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_599852 prefixEnd_599852 := by exact prefixLift 599852
  have htrace : WordTrace (prefixWord ++ tailWord_599852) baseStart_599852 baseEnd_599852 := by
    simpa [prefixWord, tailWord_599852, baseEnd_599852] using wordTrace_append hprefix tailTrace_599852
  have hstable : (prefixWord ++ tailWord_599852).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599852).length < 2 ^ (prefixWord ++ tailWord_599852).sum := by decide
  have hdescent : baseEnd_599852 < baseStart_599852 := by decide
  rcases family_descends (prefixWord ++ tailWord_599852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599859 : List Nat := [1, 1, 1, 2, 7, 1, 2, 1, 4]
def baseStart_599859 : Nat := 118140960795 + 599859 * 2 ^ 59
def prefixEnd_599859 : Nat := 4983230072969 + 3 ^ 40 * 599859 * 2
def baseEnd_599859 : Nat := 273791992822643362314493

theorem tailTrace_599859 : CollatzResearch.WordTrace tailWord_599859 prefixEnd_599859 273791992822643362314493 := by
  unfold tailWord_599859
  simp only [CollatzResearch.WordTrace]
  refine ⟨21878655133820765606026631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14585770089213843737351087 21878655133820765606026631)
  ·
    refine ⟨32817982700731148409039947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21878655133820765606026631 32817982700731148409039947)
    ·
      refine ⟨49226974051096722613559921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32817982700731148409039947 49226974051096722613559921)
      ·
        refine ⟨36920230538322541960169941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49226974051096722613559921 36920230538322541960169941)
        ·
          refine ⟨865317903241934577191483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 36920230538322541960169941 865317903241934577191483)
          ·
            refine ⟨1297976854862901865787225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 865317903241934577191483 1297976854862901865787225)
            ·
              refine ⟨973482641147176399340419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1297976854862901865787225 973482641147176399340419)
              ·
                refine ⟨1460223961720764599010629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 973482641147176399340419 1460223961720764599010629)
                ·
                  refine ⟨273791992822643362314493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1460223961720764599010629 273791992822643362314493)
                  ·
                    rfl

theorem cell20_599859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 1, 4].length) (baseStart_599859 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_599859 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_599859 prefixEnd_599859 := by exact prefixLift 599859
  have htrace : WordTrace (prefixWord ++ tailWord_599859) baseStart_599859 baseEnd_599859 := by
    simpa [prefixWord, tailWord_599859, baseEnd_599859] using wordTrace_append hprefix tailTrace_599859
  have hstable : (prefixWord ++ tailWord_599859).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599859).length < 2 ^ (prefixWord ++ tailWord_599859).sum := by decide
  have hdescent : baseEnd_599859 < baseStart_599859 := by decide
  rcases family_descends (prefixWord ++ tailWord_599859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599869 : List Nat := [1, 4, 1, 4, 1, 2, 3, 1, 3]
def baseStart_599869 : Nat := 118140960795 + 599869 * 2 ^ 59
def prefixEnd_599869 : Nat := 4983230072969 + 3 ^ 40 * 599869 * 2
def baseEnd_599869 : Nat := 273796557095127771981119

theorem tailTrace_599869 : CollatzResearch.WordTrace tailWord_599869 prefixEnd_599869 273796557095127771981119 := by
  unfold tailWord_599869
  simp only [CollatzResearch.WordTrace]
  refine ⟨21879019863784537313890661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14586013242523024875927107 21879019863784537313890661)
  ·
    refine ⟨4102316224459600746354499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21879019863784537313890661 4102316224459600746354499)
    ·
      refine ⟨6153474336689401119531749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4102316224459600746354499 6153474336689401119531749)
      ·
        refine ⟨1153776438129262709912203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6153474336689401119531749 1153776438129262709912203)
        ·
          refine ⟨1730664657193894064868305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1153776438129262709912203 1730664657193894064868305)
          ·
            refine ⟨1297998492895420548651229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1730664657193894064868305 1297998492895420548651229)
            ·
              refine ⟨486749434835782705744211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1297998492895420548651229 486749434835782705744211)
              ·
                refine ⟨730124152253674058616317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 486749434835782705744211 730124152253674058616317)
                ·
                  refine ⟨273796557095127771981119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 730124152253674058616317 273796557095127771981119)
                  ·
                    rfl

theorem cell20_599869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 3, 1, 3].length) (baseStart_599869 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_599869 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_599869 prefixEnd_599869 := by exact prefixLift 599869
  have htrace : WordTrace (prefixWord ++ tailWord_599869) baseStart_599869 baseEnd_599869 := by
    simpa [prefixWord, tailWord_599869, baseEnd_599869] using wordTrace_append hprefix tailTrace_599869
  have hstable : (prefixWord ++ tailWord_599869).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599869).length < 2 ^ (prefixWord ++ tailWord_599869).sum := by decide
  have hdescent : baseEnd_599869 < baseStart_599869 := by decide
  rcases family_descends (prefixWord ++ tailWord_599869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599880 : List Nat := [2, 1, 3, 1, 1, 4, 2, 2, 4]
def baseStart_599880 : Nat := 118140960795 + 599880 * 2 ^ 59
def prefixEnd_599880 : Nat := 4983230072969 + 3 ^ 40 * 599880 * 2
def baseEnd_599880 : Nat := 273801577794860622614407

theorem tailTrace_599880 : CollatzResearch.WordTrace tailWord_599880 prefixEnd_599880 273801577794860622614407 := by
  unfold tailWord_599880
  simp only [CollatzResearch.WordTrace]
  refine ⟨10939710533372343096270547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14586280711163124128360729 10939710533372343096270547)
  ·
    refine ⟨16409565800058514644405821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10939710533372343096270547 16409565800058514644405821)
    ·
      refine ⟨6153587175021942991652183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16409565800058514644405821 6153587175021942991652183)
      ·
        refine ⟨9230380762532914487478275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6153587175021942991652183 9230380762532914487478275)
        ·
          refine ⟨13845571143799371731217413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9230380762532914487478275 13845571143799371731217413)
          ·
            refine ⟨2596044589462382199603265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13845571143799371731217413 2596044589462382199603265)
            ·
              refine ⟨1947033442096786649702449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2596044589462382199603265 1947033442096786649702449)
              ·
                refine ⟨1460275081572589987276837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1947033442096786649702449 1460275081572589987276837)
                ·
                  refine ⟨273801577794860622614407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1460275081572589987276837 273801577794860622614407)
                  ·
                    rfl

theorem cell20_599880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 2, 4].length) (baseStart_599880 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_599880 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_599880 prefixEnd_599880 := by exact prefixLift 599880
  have htrace : WordTrace (prefixWord ++ tailWord_599880) baseStart_599880 baseEnd_599880 := by
    simpa [prefixWord, tailWord_599880, baseEnd_599880] using wordTrace_append hprefix tailTrace_599880
  have hstable : (prefixWord ++ tailWord_599880).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599880).length < 2 ^ (prefixWord ++ tailWord_599880).sum := by decide
  have hdescent : baseEnd_599880 < baseStart_599880 := by decide
  rcases family_descends (prefixWord ++ tailWord_599880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599911 : List Nat := [1, 1, 5, 1, 2, 1, 2, 4, 3]
def baseStart_599911 : Nat := 118140960795 + 599911 * 2 ^ 59
def prefixEnd_599911 : Nat := 4983230072969 + 3 ^ 40 * 599911 * 2
def baseEnd_599911 : Nat := 273815727039562292580947

theorem tailTrace_599911 : CollatzResearch.WordTrace tailWord_599911 prefixEnd_599911 273815727039562292580947 := by
  unfold tailWord_599911
  simp only [CollatzResearch.WordTrace]
  refine ⟨21880551729632378486919587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14587034486421585657946391 21880551729632378486919587)
  ·
    refine ⟨32820827594448567730379381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21880551729632378486919587 32820827594448567730379381)
    ·
      refine ⟨3076952586979553224723067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32820827594448567730379381 3076952586979553224723067)
      ·
        refine ⟨4615428880469329837084601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3076952586979553224723067 4615428880469329837084601)
        ·
          refine ⟨3461571660351997377813451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4615428880469329837084601 3461571660351997377813451)
          ·
            refine ⟨5192357490527996066720177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3461571660351997377813451 5192357490527996066720177)
            ·
              refine ⟨3894268117895997050040133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5192357490527996066720177 3894268117895997050040133)
              ·
                refine ⟨730175272105499446882525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3894268117895997050040133 730175272105499446882525)
                ·
                  refine ⟨273815727039562292580947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 730175272105499446882525 273815727039562292580947)
                  ·
                    rfl

theorem cell20_599911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 4, 3].length) (baseStart_599911 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_599911 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_599911 prefixEnd_599911 := by exact prefixLift 599911
  have htrace : WordTrace (prefixWord ++ tailWord_599911) baseStart_599911 baseEnd_599911 := by
    simpa [prefixWord, tailWord_599911, baseEnd_599911] using wordTrace_append hprefix tailTrace_599911
  have hstable : (prefixWord ++ tailWord_599911).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599911).length < 2 ^ (prefixWord ++ tailWord_599911).sum := by decide
  have hdescent : baseEnd_599911 < baseStart_599911 := by decide
  rcases family_descends (prefixWord ++ tailWord_599911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599976 : List Nat := [2, 1, 6, 2, 1, 2, 1, 5]
def baseStart_599976 : Nat := 118140960795 + 599976 * 2 ^ 59
def prefixEnd_599976 : Nat := 4983230072969 + 3 ^ 40 * 599976 * 2
def baseEnd_599976 : Nat := 91281798270236985138005

theorem tailTrace_599976 : CollatzResearch.WordTrace tailWord_599976 prefixEnd_599976 91281798270236985138005 := by
  unfold tailWord_599976
  simp only [CollatzResearch.WordTrace]
  refine ⟨10941461237198447294017891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14588614982931263058690521 10941461237198447294017891)
  ·
    refine ⟨16412191855797670941026837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10941461237198447294017891 16412191855797670941026837)
    ·
      refine ⟨769321493240515825360633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 16412191855797670941026837 769321493240515825360633)
      ·
        refine ⟨576991119930386869020475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 769321493240515825360633 576991119930386869020475)
        ·
          refine ⟨865486679895580303530713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 576991119930386869020475 865486679895580303530713)
          ·
            refine ⟨649115009921685227648035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 865486679895580303530713 649115009921685227648035)
            ·
              refine ⟨973672514882527841472053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 649115009921685227648035 973672514882527841472053)
              ·
                refine ⟨91281798270236985138005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 973672514882527841472053 91281798270236985138005)
                ·
                  rfl

theorem cell20_599976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 5].length) (baseStart_599976 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_599976 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_599976 prefixEnd_599976 := by exact prefixLift 599976
  have htrace : WordTrace (prefixWord ++ tailWord_599976) baseStart_599976 baseEnd_599976 := by
    simpa [prefixWord, tailWord_599976, baseEnd_599976] using wordTrace_append hprefix tailTrace_599976
  have hstable : (prefixWord ++ tailWord_599976).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599976).length < 2 ^ (prefixWord ++ tailWord_599976).sum := by decide
  have hdescent : baseEnd_599976 < baseStart_599976 := by decide
  rcases family_descends (prefixWord ++ tailWord_599976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600011 : List Nat := [1, 1, 1, 1, 3, 4, 4, 3, 2]
def baseStart_600011 : Nat := 118140960795 + 600011 * 2 ^ 59
def prefixEnd_600011 : Nat := 4983230072969 + 3 ^ 40 * 600011 * 2
def baseEnd_600011 : Nat := 273861369764406389247205

theorem tailTrace_600011 : CollatzResearch.WordTrace tailWord_600011 prefixEnd_600011 273861369764406389247205 := by
  unfold tailWord_600011
  simp only [CollatzResearch.WordTrace]
  refine ⟨21884199029270095565559887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14589466019513397043706591 21884199029270095565559887)
  ·
    refine ⟨32826298543905143348339831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21884199029270095565559887 32826298543905143348339831)
    ·
      refine ⟨49239447815857715022509747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32826298543905143348339831 49239447815857715022509747)
      ·
        refine ⟨73859171723786572533764621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49239447815857715022509747 73859171723786572533764621)
        ·
          refine ⟨27697189396419964700161733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73859171723786572533764621 27697189396419964700161733)
          ·
            refine ⟨5193223011828743381280325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27697189396419964700161733 5193223011828743381280325)
            ·
              refine ⟨973729314717889383990061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5193223011828743381280325 973729314717889383990061)
              ·
                refine ⟨365148493019208518996273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 973729314717889383990061 365148493019208518996273)
                ·
                  refine ⟨273861369764406389247205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 365148493019208518996273 273861369764406389247205)
                  ·
                    rfl

theorem cell20_600011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 3, 2].length) (baseStart_600011 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_600011 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_600011 prefixEnd_600011 := by exact prefixLift 600011
  have htrace : WordTrace (prefixWord ++ tailWord_600011) baseStart_600011 baseEnd_600011 := by
    simpa [prefixWord, tailWord_600011, baseEnd_600011] using wordTrace_append hprefix tailTrace_600011
  have hstable : (prefixWord ++ tailWord_600011).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600011).length < 2 ^ (prefixWord ++ tailWord_600011).sum := by decide
  have hdescent : baseEnd_600011 < baseStart_600011 := by decide
  rcases family_descends (prefixWord ++ tailWord_600011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600015 : List Nat := [1, 1, 2, 1, 1, 5, 1, 2, 6]
def baseStart_600015 : Nat := 118140960795 + 600015 * 2 ^ 59
def prefixEnd_600015 : Nat := 4983230072969 + 3 ^ 40 * 600015 * 2
def baseEnd_600015 : Nat := 273863195473400153113855

theorem tailTrace_600015 : CollatzResearch.WordTrace tailWord_600015 prefixEnd_600015 273863195473400153113855 := by
  unfold tailWord_600015
  simp only [CollatzResearch.WordTrace]
  refine ⟨21884344921255604248705499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14589563280837069499136999 21884344921255604248705499)
  ·
    refine ⟨32826517381883406373058249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21884344921255604248705499 32826517381883406373058249)
    ·
      refine ⟨24619888036412554779793687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32826517381883406373058249 24619888036412554779793687)
      ·
        refine ⟨36929832054618832169690531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24619888036412554779793687 36929832054618832169690531)
        ·
          refine ⟨55394748081928248254535797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36929832054618832169690531 55394748081928248254535797)
          ·
            refine ⟨5193257632680773273862731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55394748081928248254535797 5193257632680773273862731)
            ·
              refine ⟨7789886449021159910794097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5193257632680773273862731 7789886449021159910794097)
              ·
                refine ⟨5842414836765869933095573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7789886449021159910794097 5842414836765869933095573)
                ·
                  refine ⟨273863195473400153113855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5842414836765869933095573 273863195473400153113855)
                  ·
                    rfl

theorem cell20_600015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 6].length) (baseStart_600015 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_600015 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_600015 prefixEnd_600015 := by exact prefixLift 600015
  have htrace : WordTrace (prefixWord ++ tailWord_600015) baseStart_600015 baseEnd_600015 := by
    simpa [prefixWord, tailWord_600015, baseEnd_600015] using wordTrace_append hprefix tailTrace_600015
  have hstable : (prefixWord ++ tailWord_600015).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600015).length < 2 ^ (prefixWord ++ tailWord_600015).sum := by decide
  have hdescent : baseEnd_600015 < baseStart_600015 := by decide
  rcases family_descends (prefixWord ++ tailWord_600015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600018 : List Nat := [3, 2, 2, 3, 2, 1, 7]
def baseStart_600018 : Nat := 118140960795 + 600018 * 2 ^ 59
def prefixEnd_600018 : Nat := 4983230072969 + 3 ^ 40 * 600018 * 2
def baseEnd_600018 : Nat := 30429396083905052890427

theorem tailTrace_600018 : CollatzResearch.WordTrace tailWord_600018 prefixEnd_600018 30429396083905052890427 := by
  unfold tailWord_600018
  simp only [CollatzResearch.WordTrace]
  refine ⟨5471113585061183940266177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14589636226829823840709805 5471113585061183940266177)
  ·
    refine ⟨4103335188795887955199633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5471113585061183940266177 4103335188795887955199633)
    ·
      refine ⟨3077501391596915966399725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4103335188795887955199633 3077501391596915966399725)
      ·
        refine ⟨1154063021848843487399897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3077501391596915966399725 1154063021848843487399897)
        ·
          refine ⟨865547266386632615549923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1154063021848843487399897 865547266386632615549923)
          ·
            refine ⟨1298320899579948923324885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 865547266386632615549923 1298320899579948923324885)
            ·
              refine ⟨30429396083905052890427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1298320899579948923324885 30429396083905052890427)
              ·
                rfl

theorem cell20_600018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 7].length) (baseStart_600018 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_600018 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_600018 prefixEnd_600018 := by exact prefixLift 600018
  have htrace : WordTrace (prefixWord ++ tailWord_600018) baseStart_600018 baseEnd_600018 := by
    simpa [prefixWord, tailWord_600018, baseEnd_600018] using wordTrace_append hprefix tailTrace_600018
  have hstable : (prefixWord ++ tailWord_600018).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600018).length < 2 ^ (prefixWord ++ tailWord_600018).sum := by decide
  have hdescent : baseEnd_600018 < baseStart_600018 := by decide
  rcases family_descends (prefixWord ++ tailWord_600018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600025 : List Nat := [1, 2, 1, 2, 6, 1, 1, 1, 5]
def baseStart_600025 : Nat := 118140960795 + 600025 * 2 ^ 59
def prefixEnd_600025 : Nat := 4983230072969 + 3 ^ 40 * 600025 * 2
def baseEnd_600025 : Nat := 273867759745884562780481

theorem tailTrace_600025 : CollatzResearch.WordTrace tailWord_600025 prefixEnd_600025 273867759745884562780481 := by
  unfold tailWord_600025
  simp only [CollatzResearch.WordTrace]
  refine ⟨21884709651219375956569529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14589806434146250637713019 21884709651219375956569529)
  ·
    refine ⟨16413532238414531967427147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21884709651219375956569529 16413532238414531967427147)
    ·
      refine ⟨24620298357621797951140721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16413532238414531967427147 24620298357621797951140721)
      ·
        refine ⟨18465223768216348463355541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24620298357621797951140721 18465223768216348463355541)
        ·
          refine ⟨865557364135141334219791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 18465223768216348463355541 865557364135141334219791)
          ·
            refine ⟨1298336046202712001329687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 865557364135141334219791 1298336046202712001329687)
            ·
              refine ⟨1947504069304068001994531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1298336046202712001329687 1947504069304068001994531)
              ·
                refine ⟨2921256103956102002991797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1947504069304068001994531 2921256103956102002991797)
                ·
                  refine ⟨273867759745884562780481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2921256103956102002991797 273867759745884562780481)
                  ·
                    rfl

theorem cell20_600025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 5].length) (baseStart_600025 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_600025 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_600025 prefixEnd_600025 := by exact prefixLift 600025
  have htrace : WordTrace (prefixWord ++ tailWord_600025) baseStart_600025 baseEnd_600025 := by
    simpa [prefixWord, tailWord_600025, baseEnd_600025] using wordTrace_append hprefix tailTrace_600025
  have hstable : (prefixWord ++ tailWord_600025).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600025).length < 2 ^ (prefixWord ++ tailWord_600025).sum := by decide
  have hdescent : baseEnd_600025 < baseStart_600025 := by decide
  rcases family_descends (prefixWord ++ tailWord_600025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600042 : List Nat := [3, 1, 3, 1, 2, 1, 5, 1, 3]
def baseStart_600042 : Nat := 118140960795 + 600042 * 2 ^ 59
def prefixEnd_600042 : Nat := 4983230072969 + 3 ^ 40 * 600042 * 2
def baseEnd_600042 : Nat := 273875519009108059213745

theorem tailTrace_600042 : CollatzResearch.WordTrace tailWord_600042 prefixEnd_600042 273875519009108059213745 := by
  unfold tailWord_600042
  simp only [CollatzResearch.WordTrace]
  refine ⟨5471332423039446964984595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14590219794771858573292253 5471332423039446964984595)
  ·
    refine ⟨8206998634559170447476893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5471332423039446964984595 8206998634559170447476893)
    ·
      refine ⟨3077624487959688917803835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8206998634559170447476893 3077624487959688917803835)
      ·
        refine ⟨4616436731939533376705753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3077624487959688917803835 4616436731939533376705753)
        ·
          refine ⟨3462327548954650032529315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4616436731939533376705753 3462327548954650032529315)
          ·
            refine ⟨5193491323431975048793973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3462327548954650032529315 5193491323431975048793973)
            ·
              refine ⟨486889811571747660824435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5193491323431975048793973 486889811571747660824435)
              ·
                refine ⟨730334717357621491236653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 486889811571747660824435 730334717357621491236653)
                ·
                  refine ⟨273875519009108059213745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 730334717357621491236653 273875519009108059213745)
                  ·
                    rfl

theorem cell20_600042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 5, 1, 3].length) (baseStart_600042 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_600042 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_600042 prefixEnd_600042 := by exact prefixLift 600042
  have htrace : WordTrace (prefixWord ++ tailWord_600042) baseStart_600042 baseEnd_600042 := by
    simpa [prefixWord, tailWord_600042, baseEnd_600042] using wordTrace_append hprefix tailTrace_600042
  have hstable : (prefixWord ++ tailWord_600042).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600042).length < 2 ^ (prefixWord ++ tailWord_600042).sum := by decide
  have hdescent : baseEnd_600042 < baseStart_600042 := by decide
  rcases family_descends (prefixWord ++ tailWord_600042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600091 : List Nat := [1, 1, 1, 1, 1, 1, 3, 7, 4]
def baseStart_600091 : Nat := 118140960795 + 600091 * 2 ^ 59
def prefixEnd_600091 : Nat := 4983230072969 + 3 ^ 40 * 600091 * 2
def baseEnd_600091 : Nat := 273897883944281666580211

theorem tailTrace_600091 : CollatzResearch.WordTrace tailWord_600091 prefixEnd_600091 273897883944281666580211 := by
  unfold tailWord_600091
  simp only [CollatzResearch.WordTrace]
  refine ⟨21887116868980269228472127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14591411245986846152314751 21887116868980269228472127)
  ·
    refine ⟨32830675303470403842708191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21887116868980269228472127 32830675303470403842708191)
    ·
      refine ⟨49246012955205605764062287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32830675303470403842708191 49246012955205605764062287)
      ·
        refine ⟨73869019432808408646093431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49246012955205605764062287 73869019432808408646093431)
        ·
          refine ⟨110803529149212612969140147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73869019432808408646093431 110803529149212612969140147)
          ·
            refine ⟨166205293723818919453710221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110803529149212612969140147 166205293723818919453710221)
            ·
              refine ⟨62326985146432094795141333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 166205293723818919453710221 62326985146432094795141333)
              ·
                refine ⟨1460788714369502221761125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 62326985146432094795141333 1460788714369502221761125)
                ·
                  refine ⟨273897883944281666580211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1460788714369502221761125 273897883944281666580211)
                  ·
                    rfl

theorem cell20_600091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7, 4].length) (baseStart_600091 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_600091 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_600091 prefixEnd_600091 := by exact prefixLift 600091
  have htrace : WordTrace (prefixWord ++ tailWord_600091) baseStart_600091 baseEnd_600091 := by
    simpa [prefixWord, tailWord_600091, baseEnd_600091] using wordTrace_append hprefix tailTrace_600091
  have hstable : (prefixWord ++ tailWord_600091).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600091).length < 2 ^ (prefixWord ++ tailWord_600091).sum := by decide
  have hdescent : baseEnd_600091 < baseStart_600091 := by decide
  rcases family_descends (prefixWord ++ tailWord_600091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600097 : List Nat := [1, 2, 3, 2, 4, 2, 2, 1, 3]
def baseStart_600097 : Nat := 118140960795 + 600097 * 2 ^ 59
def prefixEnd_600097 : Nat := 4983230072969 + 3 ^ 40 * 600097 * 2
def baseEnd_600097 : Nat := 273900622507772312380187

theorem tailTrace_600097 : CollatzResearch.WordTrace tailWord_600097 prefixEnd_600097 273900622507772312380187 := by
  unfold tailWord_600097
  simp only [CollatzResearch.WordTrace]
  refine ⟨21887335706958532253190545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14591557137972354835460363 21887335706958532253190545)
  ·
    refine ⟨16415501780218899189892909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21887335706958532253190545 16415501780218899189892909)
    ·
      refine ⟨6155813167582087196209841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16415501780218899189892909 6155813167582087196209841)
      ·
        refine ⟨4616859875686565397157381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6155813167582087196209841 4616859875686565397157381)
        ·
          refine ⟨865661226691231011967009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4616859875686565397157381 865661226691231011967009)
          ·
            refine ⟨649245920018423258975257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 865661226691231011967009 649245920018423258975257)
            ·
              refine ⟨486934440013817444231443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 649245920018423258975257 486934440013817444231443)
              ·
                refine ⟨730401660020726166347165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 486934440013817444231443 730401660020726166347165)
                ·
                  refine ⟨273900622507772312380187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 730401660020726166347165 273900622507772312380187)
                  ·
                    rfl

theorem cell20_600097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 2, 1, 3].length) (baseStart_600097 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_600097 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_600097 prefixEnd_600097 := by exact prefixLift 600097
  have htrace : WordTrace (prefixWord ++ tailWord_600097) baseStart_600097 baseEnd_600097 := by
    simpa [prefixWord, tailWord_600097, baseEnd_600097] using wordTrace_append hprefix tailTrace_600097
  have hstable : (prefixWord ++ tailWord_600097).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600097).length < 2 ^ (prefixWord ++ tailWord_600097).sum := by decide
  have hdescent : baseEnd_600097 < baseStart_600097 := by decide
  rcases family_descends (prefixWord ++ tailWord_600097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600101 : List Nat := [1, 3, 1, 2, 2, 4, 1, 3, 3]
def baseStart_600101 : Nat := 118140960795 + 600101 * 2 ^ 59
def prefixEnd_600101 : Nat := 4983230072969 + 3 ^ 40 * 600101 * 2
def baseEnd_600101 : Nat := 273902448216766076246837

theorem tailTrace_600101 : CollatzResearch.WordTrace tailWord_600101 prefixEnd_600101 273902448216766076246837 := by
  unfold tailWord_600101
  simp only [CollatzResearch.WordTrace]
  refine ⟨21887481598944040936336157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14591654399296027290890771 21887481598944040936336157)
  ·
    refine ⟨8207805599604015351126059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21887481598944040936336157 8207805599604015351126059)
    ·
      refine ⟨12311708399406023026689089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8207805599604015351126059 12311708399406023026689089)
      ·
        refine ⟨9233781299554517270016817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12311708399406023026689089 9233781299554517270016817)
        ·
          refine ⟨6925335974665887952512613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9233781299554517270016817 6925335974665887952512613)
          ·
            refine ⟨1298500495249853991096115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6925335974665887952512613 1298500495249853991096115)
            ·
              refine ⟨1947750742874780986644173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1298500495249853991096115 1947750742874780986644173)
              ·
                refine ⟨730406528578042869991565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1947750742874780986644173 730406528578042869991565)
                ·
                  refine ⟨273902448216766076246837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 730406528578042869991565 273902448216766076246837)
                  ·
                    rfl

theorem cell20_600101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 3, 3].length) (baseStart_600101 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_600101 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_600101 prefixEnd_600101 := by exact prefixLift 600101
  have htrace : WordTrace (prefixWord ++ tailWord_600101) baseStart_600101 baseEnd_600101 := by
    simpa [prefixWord, tailWord_600101, baseEnd_600101] using wordTrace_append hprefix tailTrace_600101
  have hstable : (prefixWord ++ tailWord_600101).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600101).length < 2 ^ (prefixWord ++ tailWord_600101).sum := by decide
  have hdescent : baseEnd_600101 < baseStart_600101 := by decide
  rcases family_descends (prefixWord ++ tailWord_600101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600125 : List Nat := [1, 4, 1, 3, 1, 1, 2, 5, 2]
def baseStart_600125 : Nat := 118140960795 + 600125 * 2 ^ 59
def prefixEnd_600125 : Nat := 4983230072969 + 3 ^ 40 * 600125 * 2
def baseEnd_600125 : Nat := 273913402470728659446739

theorem tailTrace_600125 : CollatzResearch.WordTrace tailWord_600125 prefixEnd_600125 273913402470728659446739 := by
  unfold tailWord_600125
  simp only [CollatzResearch.WordTrace]
  refine ⟨21888356950857093035209829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14592237967238062023473219 21888356950857093035209829)
  ·
    refine ⟨4104066928285704944101843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21888356950857093035209829 4104066928285704944101843)
    ·
      refine ⟨6156100392428557416152765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4104066928285704944101843 6156100392428557416152765)
      ·
        refine ⟨2308537647160709031057287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6156100392428557416152765 2308537647160709031057287)
        ·
          refine ⟨3462806470741063546585931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2308537647160709031057287 3462806470741063546585931)
          ·
            refine ⟨5194209706111595319878897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3462806470741063546585931 5194209706111595319878897)
            ·
              refine ⟨3895657279583696489909173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5194209706111595319878897 3895657279583696489909173)
              ·
                refine ⟨365217869960971545928985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3895657279583696489909173 365217869960971545928985)
                ·
                  refine ⟨273913402470728659446739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 365217869960971545928985 273913402470728659446739)
                  ·
                    rfl

theorem cell20_600125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 5, 2].length) (baseStart_600125 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_600125 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_600125 prefixEnd_600125 := by exact prefixLift 600125
  have htrace : WordTrace (prefixWord ++ tailWord_600125) baseStart_600125 baseEnd_600125 := by
    simpa [prefixWord, tailWord_600125, baseEnd_600125] using wordTrace_append hprefix tailTrace_600125
  have hstable : (prefixWord ++ tailWord_600125).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600125).length < 2 ^ (prefixWord ++ tailWord_600125).sum := by decide
  have hdescent : baseEnd_600125 < baseStart_600125 := by decide
  rcases family_descends (prefixWord ++ tailWord_600125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600142 : List Nat := [4, 1, 1, 1, 1, 4, 4, 2, 2]
def baseStart_600142 : Nat := 118140960795 + 600142 * 2 ^ 59
def prefixEnd_600142 : Nat := 4983230072969 + 3 ^ 40 * 600142 * 2
def baseEnd_600142 : Nat := 273921161733952155880003

theorem tailTrace_600142 : CollatzResearch.WordTrace tailWord_600142 prefixEnd_600142 273921161733952155880003 := by
  unfold tailWord_600142
  simp only [CollatzResearch.WordTrace]
  refine ⟨2736122123974438117322335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14592651327863669959052453 2736122123974438117322335)
  ·
    refine ⟨4104183185961657175983503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2736122123974438117322335 4104183185961657175983503)
    ·
      refine ⟨6156274778942485763975255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4104183185961657175983503 6156274778942485763975255)
      ·
        refine ⟨9234412168413728645962883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6156274778942485763975255 9234412168413728645962883)
        ·
          refine ⟨13851618252620592968944325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9234412168413728645962883 13851618252620592968944325)
          ·
            refine ⟨2597178422366361181677061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13851618252620592968944325 2597178422366361181677061)
            ·
              refine ⟨486970954193692721564449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2597178422366361181677061 486970954193692721564449)
              ·
                refine ⟨365228215645269541173337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 486970954193692721564449 365228215645269541173337)
                ·
                  refine ⟨273921161733952155880003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 365228215645269541173337 273921161733952155880003)
                  ·
                    rfl

theorem cell20_600142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 4, 2, 2].length) (baseStart_600142 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_600142 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_600142 prefixEnd_600142 := by exact prefixLift 600142
  have htrace : WordTrace (prefixWord ++ tailWord_600142) baseStart_600142 baseEnd_600142 := by
    simpa [prefixWord, tailWord_600142, baseEnd_600142] using wordTrace_append hprefix tailTrace_600142
  have hstable : (prefixWord ++ tailWord_600142).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600142).length < 2 ^ (prefixWord ++ tailWord_600142).sum := by decide
  have hdescent : baseEnd_600142 < baseStart_600142 := by decide
  rcases family_descends (prefixWord ++ tailWord_600142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600250 : List Nat := [3, 1, 1, 1, 2, 2, 10]
def baseStart_600250 : Nat := 118140960795 + 600250 * 2 ^ 59
def prefixEnd_600250 : Nat := 4983230072969 + 3 ^ 40 * 600250 * 2
def baseEnd_600250 : Nat := 30441161764087086697729

theorem tailTrace_600250 : CollatzResearch.WordTrace tailWord_600250 prefixEnd_600250 30441161764087086697729 := by
  unfold tailWord_600250
  simp only [CollatzResearch.WordTrace]
  refine ⟨5473229018851059845877551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14595277383602826255673469 5473229018851059845877551)
  ·
    refine ⟨8209843528276589768816327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5473229018851059845877551 8209843528276589768816327)
    ·
      refine ⟨12314765292414884653224491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8209843528276589768816327 12314765292414884653224491)
      ·
        refine ⟨18472147938622326979836737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12314765292414884653224491 18472147938622326979836737)
        ·
          refine ⟨13854110953966745234877553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18472147938622326979836737 13854110953966745234877553)
          ·
            refine ⟨10390583215475058926158165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13854110953966745234877553 10390583215475058926158165)
            ·
              refine ⟨30441161764087086697729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10390583215475058926158165 30441161764087086697729)
              ·
                rfl

theorem cell20_600250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 10].length) (baseStart_600250 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_600250 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_600250 prefixEnd_600250 := by exact prefixLift 600250
  have htrace : WordTrace (prefixWord ++ tailWord_600250) baseStart_600250 baseEnd_600250 := by
    simpa [prefixWord, tailWord_600250, baseEnd_600250] using wordTrace_append hprefix tailTrace_600250
  have hstable : (prefixWord ++ tailWord_600250).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600250).length < 2 ^ (prefixWord ++ tailWord_600250).sum := by decide
  have hdescent : baseEnd_600250 < baseStart_600250 := by decide
  rcases family_descends (prefixWord ++ tailWord_600250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600256 : List Nat := [2, 1, 1, 2, 5, 2, 3, 2, 2]
def baseStart_600256 : Nat := 118140960795 + 600256 * 2 ^ 59
def prefixEnd_600256 : Nat := 4983230072969 + 3 ^ 40 * 600256 * 2
def baseEnd_600256 : Nat := 273973194440274426079537

theorem tailTrace_600256 : CollatzResearch.WordTrace tailWord_600256 prefixEnd_600256 273973194440274426079537 := by
  unfold tailWord_600256
  simp only [CollatzResearch.WordTrace]
  refine ⟨10946567456691251204114311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14595423275588334938819081 10946567456691251204114311)
  ·
    refine ⟨16419851185036876806171467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10946567456691251204114311 16419851185036876806171467)
    ·
      refine ⟨24629776777555315209257201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16419851185036876806171467 24629776777555315209257201)
      ·
        refine ⟨18472332583166486406942901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24629776777555315209257201 18472332583166486406942901)
        ·
          refine ⟨1731781179671858100650897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18472332583166486406942901 1731781179671858100650897)
          ·
            refine ⟨1298835884753893575488173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1731781179671858100650897 1298835884753893575488173)
            ·
              refine ⟨487063456782710090808065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1298835884753893575488173 487063456782710090808065)
              ·
                refine ⟨365297592587032568106049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 487063456782710090808065 365297592587032568106049)
                ·
                  refine ⟨273973194440274426079537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 365297592587032568106049 273973194440274426079537)
                  ·
                    rfl

theorem cell20_600256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 3, 2, 2].length) (baseStart_600256 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_600256 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_600256 prefixEnd_600256 := by exact prefixLift 600256
  have htrace : WordTrace (prefixWord ++ tailWord_600256) baseStart_600256 baseEnd_600256 := by
    simpa [prefixWord, tailWord_600256, baseEnd_600256] using wordTrace_append hprefix tailTrace_600256
  have hstable : (prefixWord ++ tailWord_600256).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600256).length < 2 ^ (prefixWord ++ tailWord_600256).sum := by decide
  have hdescent : baseEnd_600256 < baseStart_600256 := by decide
  rcases family_descends (prefixWord ++ tailWord_600256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600270 : List Nat := [4, 1, 1, 1, 4, 1, 4, 1, 3]
def baseStart_600270 : Nat := 118140960795 + 600270 * 2 ^ 59
def prefixEnd_600270 : Nat := 4983230072969 + 3 ^ 40 * 600270 * 2
def baseEnd_600270 : Nat := 273979584421752599612813

theorem tailTrace_600270 : CollatzResearch.WordTrace tailWord_600270 prefixEnd_600270 273979584421752599612813 := by
  unfold tailWord_600270
  simp only [CollatzResearch.WordTrace]
  refine ⟨2736705691916472849904783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14595763690221188532825509 2736705691916472849904783)
  ·
    refine ⟨4105058537874709274857175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2736705691916472849904783 4105058537874709274857175)
    ·
      refine ⟨6157587806812063912285763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4105058537874709274857175 6157587806812063912285763)
      ·
        refine ⟨9236381710218095868428645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6157587806812063912285763 9236381710218095868428645)
        ·
          refine ⟨1731821570665892975330371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9236381710218095868428645 1731821570665892975330371)
          ·
            refine ⟨2597732355998839462995557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1731821570665892975330371 2597732355998839462995557)
            ·
              refine ⟨487074816749782399311667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2597732355998839462995557 487074816749782399311667)
              ·
                refine ⟨730612225124673598967501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 487074816749782399311667 730612225124673598967501)
                ·
                  refine ⟨273979584421752599612813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 730612225124673598967501 273979584421752599612813)
                  ·
                    rfl

theorem cell20_600270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 4, 1, 3].length) (baseStart_600270 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_600270 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_600270 prefixEnd_600270 := by exact prefixLift 600270
  have htrace : WordTrace (prefixWord ++ tailWord_600270) baseStart_600270 baseEnd_600270 := by
    simpa [prefixWord, tailWord_600270, baseEnd_600270] using wordTrace_append hprefix tailTrace_600270
  have hstable : (prefixWord ++ tailWord_600270).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600270).length < 2 ^ (prefixWord ++ tailWord_600270).sum := by decide
  have hdescent : baseEnd_600270 < baseStart_600270 := by decide
  rcases family_descends (prefixWord ++ tailWord_600270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600281 : List Nat := [1, 2, 1, 2, 3, 1, 2, 4, 4]
def baseStart_600281 : Nat := 118140960795 + 600281 * 2 ^ 59
def prefixEnd_600281 : Nat := 4983230072969 + 3 ^ 40 * 600281 * 2
def baseEnd_600281 : Nat := 273984605121485450246101

theorem tailTrace_600281 : CollatzResearch.WordTrace tailWord_600281 prefixEnd_600281 273984605121485450246101 := by
  unfold tailWord_600281
  simp only [CollatzResearch.WordTrace]
  refine ⟨21894046738291931677888697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14596031158861287785259131 21894046738291931677888697)
  ·
    refine ⟨16420535053718948758416523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21894046738291931677888697 16420535053718948758416523)
    ·
      refine ⟨24630802580578423137624785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16420535053718948758416523 24630802580578423137624785)
      ·
        refine ⟨18473101935433817353218589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24630802580578423137624785 18473101935433817353218589)
        ·
          refine ⟨6927413225787681507456971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18473101935433817353218589 6927413225787681507456971)
          ·
            refine ⟨10391119838681522261185457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6927413225787681507456971 10391119838681522261185457)
            ·
              refine ⟨7793339879011141695889093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10391119838681522261185457 7793339879011141695889093)
              ·
                refine ⟨1461251227314589067979205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7793339879011141695889093 1461251227314589067979205)
                ·
                  refine ⟨273984605121485450246101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1461251227314589067979205 273984605121485450246101)
                  ·
                    rfl

theorem cell20_600281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 4, 4].length) (baseStart_600281 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_600281 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_600281 prefixEnd_600281 := by exact prefixLift 600281
  have htrace : WordTrace (prefixWord ++ tailWord_600281) baseStart_600281 baseEnd_600281 := by
    simpa [prefixWord, tailWord_600281, baseEnd_600281] using wordTrace_append hprefix tailTrace_600281
  have hstable : (prefixWord ++ tailWord_600281).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600281).length < 2 ^ (prefixWord ++ tailWord_600281).sum := by decide
  have hdescent : baseEnd_600281 < baseStart_600281 := by decide
  rcases family_descends (prefixWord ++ tailWord_600281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600288 : List Nat := [2, 1, 1, 3, 1, 3, 1, 8]
def baseStart_600288 : Nat := 118140960795 + 600288 * 2 ^ 59
def prefixEnd_600288 : Nat := 4983230072969 + 3 ^ 40 * 600288 * 2
def baseEnd_600288 : Nat := 91329266704074845670913

theorem tailTrace_600288 : CollatzResearch.WordTrace tailWord_600288 prefixEnd_600288 91329266704074845670913 := by
  unfold tailWord_600288
  simp only [CollatzResearch.WordTrace]
  refine ⟨10947151024633285936696759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14596201366177714582262345 10947151024633285936696759)
  ·
    refine ⟨16420726536949928905045139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10947151024633285936696759 16420726536949928905045139)
    ·
      refine ⟨24631089805424893357567709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16420726536949928905045139 24631089805424893357567709)
      ·
        refine ⟨9236658677034335009087891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24631089805424893357567709 9236658677034335009087891)
        ·
          refine ⟨13854988015551502513631837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9236658677034335009087891 13854988015551502513631837)
          ·
            refine ⟨5195620505831813442611939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13854988015551502513631837 5195620505831813442611939)
            ·
              refine ⟨7793430758747720163917909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5195620505831813442611939 7793430758747720163917909)
              ·
                refine ⟨91329266704074845670913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7793430758747720163917909 91329266704074845670913)
                ·
                  rfl

theorem cell20_600288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 8].length) (baseStart_600288 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_600288 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_600288 prefixEnd_600288 := by exact prefixLift 600288
  have htrace : WordTrace (prefixWord ++ tailWord_600288) baseStart_600288 baseEnd_600288 := by
    simpa [prefixWord, tailWord_600288, baseEnd_600288] using wordTrace_append hprefix tailTrace_600288
  have hstable : (prefixWord ++ tailWord_600288).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600288).length < 2 ^ (prefixWord ++ tailWord_600288).sum := by decide
  have hdescent : baseEnd_600288 < baseStart_600288 := by decide
  rcases family_descends (prefixWord ++ tailWord_600288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600319 : List Nat := [1, 1, 2, 2, 1, 4, 2, 3, 4]
def baseStart_600319 : Nat := 118140960795 + 600319 * 2 ^ 59
def prefixEnd_600319 : Nat := 4983230072969 + 3 ^ 40 * 600319 * 2
def baseEnd_600319 : Nat := 274001949356926206979279

theorem tailTrace_600319 : CollatzResearch.WordTrace tailWord_600319 prefixEnd_600319 274001949356926206979279 := by
  unfold tailWord_600319
  simp only [CollatzResearch.WordTrace]
  refine ⟨21895432712154264167772011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14596955141436176111848007 21895432712154264167772011)
  ·
    refine ⟨32843149068231396251658017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21895432712154264167772011 32843149068231396251658017)
    ·
      refine ⟨24632361801173547188743513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32843149068231396251658017 24632361801173547188743513)
      ·
        refine ⟨18474271350880160391557635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24632361801173547188743513 18474271350880160391557635)
        ·
          refine ⟨27711407026320240587336453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18474271350880160391557635 27711407026320240587336453)
          ·
            refine ⟨5195888817435045110125585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27711407026320240587336453 5195888817435045110125585)
            ·
              refine ⟨3896916613076283832594189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5195888817435045110125585 3896916613076283832594189)
              ·
                refine ⟨1461343729903606437222821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3896916613076283832594189 1461343729903606437222821)
                ·
                  refine ⟨274001949356926206979279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1461343729903606437222821 274001949356926206979279)
                  ·
                    rfl

theorem cell20_600319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 3, 4].length) (baseStart_600319 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_600319 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_600319 prefixEnd_600319 := by exact prefixLift 600319
  have htrace : WordTrace (prefixWord ++ tailWord_600319) baseStart_600319 baseEnd_600319 := by
    simpa [prefixWord, tailWord_600319, baseEnd_600319] using wordTrace_append hprefix tailTrace_600319
  have hstable : (prefixWord ++ tailWord_600319).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600319).length < 2 ^ (prefixWord ++ tailWord_600319).sum := by decide
  have hdescent : baseEnd_600319 < baseStart_600319 := by decide
  rcases family_descends (prefixWord ++ tailWord_600319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600322 : List Nat := [3, 4, 1, 1, 2, 1, 3, 5]
def baseStart_600322 : Nat := 118140960795 + 600322 * 2 ^ 59
def prefixEnd_600322 : Nat := 4983230072969 + 3 ^ 40 * 600322 * 2
def baseEnd_600322 : Nat := 91334439546223843293089

theorem tailTrace_600322 : CollatzResearch.WordTrace tailWord_600322 prefixEnd_600322 91334439546223843293089 := by
  unfold tailWord_600322
  simp only [CollatzResearch.WordTrace]
  refine ⟨5473885532785848920032805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14597028087428930453420813 5473885532785848920032805)
  ·
    refine ⟨1026353537397346672506151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5473885532785848920032805 1026353537397346672506151)
    ·
      refine ⟨1539530306096020008759227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1026353537397346672506151 1539530306096020008759227)
      ·
        refine ⟨2309295459144030013138841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1539530306096020008759227 2309295459144030013138841)
        ·
          refine ⟨1731971594358022509854131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2309295459144030013138841 1731971594358022509854131)
          ·
            refine ⟨2597957391537033764781197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1731971594358022509854131 2597957391537033764781197)
            ·
              refine ⟨974234021826387661792949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2597957391537033764781197 974234021826387661792949)
              ·
                refine ⟨91334439546223843293089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 974234021826387661792949 91334439546223843293089)
                ·
                  rfl

theorem cell20_600322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 5].length) (baseStart_600322 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_600322 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_600322 prefixEnd_600322 := by exact prefixLift 600322
  have htrace : WordTrace (prefixWord ++ tailWord_600322) baseStart_600322 baseEnd_600322 := by
    simpa [prefixWord, tailWord_600322, baseEnd_600322] using wordTrace_append hprefix tailTrace_600322
  have hstable : (prefixWord ++ tailWord_600322).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600322).length < 2 ^ (prefixWord ++ tailWord_600322).sum := by decide
  have hdescent : baseEnd_600322 < baseStart_600322 := by decide
  rcases family_descends (prefixWord ++ tailWord_600322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600359 : List Nat := [1, 1, 8, 1, 2, 1, 1, 2, 3]
def baseStart_600359 : Nat := 118140960795 + 600359 * 2 ^ 59
def prefixEnd_600359 : Nat := 4983230072969 + 3 ^ 40 * 600359 * 2
def baseEnd_600359 : Nat := 274020206446863845645783

theorem tailTrace_600359 : CollatzResearch.WordTrace tailWord_600359 prefixEnd_600359 274020206446863845645783 := by
  unfold tailWord_600359
  simp only [CollatzResearch.WordTrace]
  refine ⟨21896891632009350999228131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14597927754672900666152087 21896891632009350999228131)
  ·
    refine ⟨32845337448014026498842197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21896891632009350999228131 32845337448014026498842197)
    ·
      refine ⟨384906298218914373033307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 32845337448014026498842197 384906298218914373033307)
      ·
        refine ⟨577359447328371559549961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 384906298218914373033307 577359447328371559549961)
        ·
          refine ⟨433019585496278669662471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 577359447328371559549961 433019585496278669662471)
          ·
            refine ⟨649529378244418004493707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 433019585496278669662471 649529378244418004493707)
            ·
              refine ⟨974294067366627006740561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 649529378244418004493707 974294067366627006740561)
              ·
                refine ⟨730720550524970255055421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 974294067366627006740561 730720550524970255055421)
                ·
                  refine ⟨274020206446863845645783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 730720550524970255055421 274020206446863845645783)
                  ·
                    rfl

theorem cell20_600359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 2, 3].length) (baseStart_600359 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_600359 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_600359 prefixEnd_600359 := by exact prefixLift 600359
  have htrace : WordTrace (prefixWord ++ tailWord_600359) baseStart_600359 baseEnd_600359 := by
    simpa [prefixWord, tailWord_600359, baseEnd_600359] using wordTrace_append hprefix tailTrace_600359
  have hstable : (prefixWord ++ tailWord_600359).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600359).length < 2 ^ (prefixWord ++ tailWord_600359).sum := by decide
  have hdescent : baseEnd_600359 < baseStart_600359 := by decide
  rcases family_descends (prefixWord ++ tailWord_600359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600443 : List Nat := [1, 1, 1, 1, 1, 7, 4, 1, 3]
def baseStart_600443 : Nat := 118140960795 + 600443 * 2 ^ 59
def prefixEnd_600443 : Nat := 4983230072969 + 3 ^ 40 * 600443 * 2
def baseEnd_600443 : Nat := 274058546335732886845439

theorem tailTrace_600443 : CollatzResearch.WordTrace tailWord_600443 prefixEnd_600443 274058546335732886845439 := by
  unfold tailWord_600443
  simp only [CollatzResearch.WordTrace]
  refine ⟨21899955363705033345285983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14599970242470022230190655 21899955363705033345285983)
  ·
    refine ⟨32849933045557550017928975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21899955363705033345285983 32849933045557550017928975)
    ·
      refine ⟨49274899568336325026893463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32849933045557550017928975 49274899568336325026893463)
      ·
        refine ⟨73912349352504487540340195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49274899568336325026893463 73912349352504487540340195)
        ·
          refine ⟨110868524028756731310510293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73912349352504487540340195 110868524028756731310510293)
          ·
            refine ⟨2598481031923985890090085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 110868524028756731310510293 2598481031923985890090085)
            ·
              refine ⟨487215193485747354391891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2598481031923985890090085 487215193485747354391891)
              ·
                refine ⟨730822790228621031587837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 487215193485747354391891 730822790228621031587837)
                ·
                  refine ⟨274058546335732886845439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 730822790228621031587837 274058546335732886845439)
                  ·
                    rfl

theorem cell20_600443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 4, 1, 3].length) (baseStart_600443 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_600443 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_600443 prefixEnd_600443 := by exact prefixLift 600443
  have htrace : WordTrace (prefixWord ++ tailWord_600443) baseStart_600443 baseEnd_600443 := by
    simpa [prefixWord, tailWord_600443, baseEnd_600443] using wordTrace_append hprefix tailTrace_600443
  have hstable : (prefixWord ++ tailWord_600443).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600443).length < 2 ^ (prefixWord ++ tailWord_600443).sum := by decide
  have hdescent : baseEnd_600443 < baseStart_600443 := by decide
  rcases family_descends (prefixWord ++ tailWord_600443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600470 : List Nat := [5, 3, 1, 2, 2, 7]
def baseStart_600470 : Nat := 118140960795 + 600470 * 2 ^ 59
def prefixEnd_600470 : Nat := 4983230072969 + 3 ^ 40 * 600470 * 2
def baseEnd_600470 : Nat := 10150772958201510849827

theorem tailTrace_600470 : CollatzResearch.WordTrace tailWord_600470 prefixEnd_600470 10150772958201510849827 := by
  unfold tailWord_600470
  simp only [CollatzResearch.WordTrace]
  refine ⟨1368808758412951059782429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14600626756404811304345909 1368808758412951059782429)
  ·
    refine ⟨513303284404856647418411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1368808758412951059782429 513303284404856647418411)
    ·
      refine ⟨769954926607284971127617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 513303284404856647418411 769954926607284971127617)
      ·
        refine ⟨577466194955463728345713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 769954926607284971127617 577466194955463728345713)
        ·
          refine ⟨433099646216597796259285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 577466194955463728345713 433099646216597796259285)
          ·
            refine ⟨10150772958201510849827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 433099646216597796259285 10150772958201510849827)
            ·
              rfl

theorem cell20_600470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 7].length) (baseStart_600470 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_600470 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_600470 prefixEnd_600470 := by exact prefixLift 600470
  have htrace : WordTrace (prefixWord ++ tailWord_600470) baseStart_600470 baseEnd_600470 := by
    simpa [prefixWord, tailWord_600470, baseEnd_600470] using wordTrace_append hprefix tailTrace_600470
  have hstable : (prefixWord ++ tailWord_600470).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600470).length < 2 ^ (prefixWord ++ tailWord_600470).sum := by decide
  have hdescent : baseEnd_600470 < baseStart_600470 := by decide
  rcases family_descends (prefixWord ++ tailWord_600470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600509 : List Nat := [1, 4, 1, 2, 2, 2, 1, 1, 6]
def baseStart_600509 : Nat := 118140960795 + 600509 * 2 ^ 59
def prefixEnd_600509 : Nat := 4983230072969 + 3 ^ 40 * 600509 * 2
def baseEnd_600509 : Nat := 274088670534129990645169

theorem tailTrace_600509 : CollatzResearch.WordTrace tailWord_600509 prefixEnd_600509 274088670534129990645169 := by
  unfold tailWord_600509
  simp only [CollatzResearch.WordTrace]
  refine ⟨21902362581465926617188581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14601575054310617744792387 21902362581465926617188581)
  ·
    refine ⟨4106692984024861240722859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21902362581465926617188581 4106692984024861240722859)
    ·
      refine ⟨6160039476037291861084289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4106692984024861240722859 6160039476037291861084289)
      ·
        refine ⟨4620029607027968895813217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6160039476037291861084289 4620029607027968895813217)
        ·
          refine ⟨3465022205270976671859913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4620029607027968895813217 3465022205270976671859913)
          ·
            refine ⟨2598766653953232503894935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3465022205270976671859913 2598766653953232503894935)
            ·
              refine ⟨3898149980929848755842403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2598766653953232503894935 3898149980929848755842403)
              ·
                refine ⟨5847224971394773133763605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3898149980929848755842403 5847224971394773133763605)
                ·
                  refine ⟨274088670534129990645169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5847224971394773133763605 274088670534129990645169)
                  ·
                    rfl

theorem cell20_600509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_600509 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_600509 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_600509 prefixEnd_600509 := by exact prefixLift 600509
  have htrace : WordTrace (prefixWord ++ tailWord_600509) baseStart_600509 baseEnd_600509 := by
    simpa [prefixWord, tailWord_600509, baseEnd_600509] using wordTrace_append hprefix tailTrace_600509
  have hstable : (prefixWord ++ tailWord_600509).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600509).length < 2 ^ (prefixWord ++ tailWord_600509).sum := by decide
  have hdescent : baseEnd_600509 < baseStart_600509 := by decide
  rcases family_descends (prefixWord ++ tailWord_600509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600523 : List Nat := [1, 1, 1, 1, 3, 3, 1, 4, 5]
def baseStart_600523 : Nat := 118140960795 + 600523 * 2 ^ 59
def prefixEnd_600523 : Nat := 4983230072969 + 3 ^ 40 * 600523 * 2
def baseEnd_600523 : Nat := 274095060515608164178445

theorem tailTrace_600523 : CollatzResearch.WordTrace tailWord_600523 prefixEnd_600523 274095060515608164178445 := by
  unfold tailWord_600523
  simp only [CollatzResearch.WordTrace]
  refine ⟨21902873203415207008198223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14601915468943471338798815 21902873203415207008198223)
  ·
    refine ⟨32854309805122810512297335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21902873203415207008198223 32854309805122810512297335)
    ·
      refine ⟨49281464707684215768446003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32854309805122810512297335 49281464707684215768446003)
      ·
        refine ⟨73922197061526323652669005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49281464707684215768446003 73922197061526323652669005)
        ·
          refine ⟨27720823898072371369750877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73922197061526323652669005 27720823898072371369750877)
          ·
            refine ⟨10395308961777139263656579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27720823898072371369750877 10395308961777139263656579)
            ·
              refine ⟨15592963442665708895484869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10395308961777139263656579 15592963442665708895484869)
              ·
                refine ⟨2923680645499820417903413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15592963442665708895484869 2923680645499820417903413)
                ·
                  refine ⟨274095060515608164178445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2923680645499820417903413 274095060515608164178445)
                  ·
                    rfl

theorem cell20_600523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 5].length) (baseStart_600523 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_600523 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_600523 prefixEnd_600523 := by exact prefixLift 600523
  have htrace : WordTrace (prefixWord ++ tailWord_600523) baseStart_600523 baseEnd_600523 := by
    simpa [prefixWord, tailWord_600523, baseEnd_600523] using wordTrace_append hprefix tailTrace_600523
  have hstable : (prefixWord ++ tailWord_600523).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600523).length < 2 ^ (prefixWord ++ tailWord_600523).sum := by decide
  have hdescent : baseEnd_600523 < baseStart_600523 := by decide
  rcases family_descends (prefixWord ++ tailWord_600523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600602 : List Nat := [3, 1, 1, 3, 1, 1, 2, 6, 2]
def baseStart_600602 : Nat := 118140960795 + 600602 * 2 ^ 59
def prefixEnd_600602 : Nat := 4983230072969 + 3 ^ 40 * 600602 * 2
def baseEnd_600602 : Nat := 274131118268235000544789

theorem tailTrace_600602 : CollatzResearch.WordTrace tailWord_600602 prefixEnd_600602 274131118268235000544789 := by
  unfold tailWord_600602
  simp only [CollatzResearch.WordTrace]
  refine ⟨5476438642532250875081015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14603836380086002333549373 5476438642532250875081015)
  ·
    refine ⟨8214657963798376312621523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5476438642532250875081015 8214657963798376312621523)
    ·
      refine ⟨12321986945697564468932285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8214657963798376312621523 12321986945697564468932285)
      ·
        refine ⟨4620745104636586675849607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12321986945697564468932285 4620745104636586675849607)
        ·
          refine ⟨6931117656954880013774411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4620745104636586675849607 6931117656954880013774411)
          ·
            refine ⟨10396676485432320020661617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6931117656954880013774411 10396676485432320020661617)
            ·
              refine ⟨7797507364074240015496213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10396676485432320020661617 7797507364074240015496213)
              ·
                refine ⟨365508157690980000726385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7797507364074240015496213 365508157690980000726385)
                ·
                  refine ⟨274131118268235000544789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 365508157690980000726385 274131118268235000544789)
                  ·
                    rfl

theorem cell20_600602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 6, 2].length) (baseStart_600602 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_600602 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_600602 prefixEnd_600602 := by exact prefixLift 600602
  have htrace : WordTrace (prefixWord ++ tailWord_600602) baseStart_600602 baseEnd_600602 := by
    simpa [prefixWord, tailWord_600602, baseEnd_600602] using wordTrace_append hprefix tailTrace_600602
  have hstable : (prefixWord ++ tailWord_600602).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600602).length < 2 ^ (prefixWord ++ tailWord_600602).sum := by decide
  have hdescent : baseEnd_600602 < baseStart_600602 := by decide
  rcases family_descends (prefixWord ++ tailWord_600602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600612 : List Nat := [2, 3, 1, 5, 1, 1, 1, 3, 3]
def baseStart_600612 : Nat := 118140960795 + 600612 * 2 ^ 59
def prefixEnd_600612 : Nat := 4983230072969 + 3 ^ 40 * 600612 * 2
def baseEnd_600612 : Nat := 274135682540719410211415

theorem tailTrace_600612 : CollatzResearch.WordTrace tailWord_600612 prefixEnd_600612 274135682540719410211415 := by
  unfold tailWord_600612
  simp only [CollatzResearch.WordTrace]
  refine ⟨10953059650046387604094045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14604079533395183472125393 10953059650046387604094045)
  ·
    refine ⟨4107397368767395351535267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10953059650046387604094045 4107397368767395351535267)
    ·
      refine ⟨6161096053151093027302901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4107397368767395351535267 6161096053151093027302901)
      ·
        refine ⟨577602754982914971309647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6161096053151093027302901 577602754982914971309647)
        ·
          refine ⟨866404132474372456964471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 577602754982914971309647 866404132474372456964471)
          ·
            refine ⟨1299606198711558685446707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 866404132474372456964471 1299606198711558685446707)
            ·
              refine ⟨1949409298067338028170061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1299606198711558685446707 1949409298067338028170061)
              ·
                refine ⟨731028486775251760563773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1949409298067338028170061 731028486775251760563773)
                ·
                  refine ⟨274135682540719410211415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 731028486775251760563773 274135682540719410211415)
                  ·
                    rfl

theorem cell20_600612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 3, 3].length) (baseStart_600612 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_600612 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_600612 prefixEnd_600612 := by exact prefixLift 600612
  have htrace : WordTrace (prefixWord ++ tailWord_600612) baseStart_600612 baseEnd_600612 := by
    simpa [prefixWord, tailWord_600612, baseEnd_600612] using wordTrace_append hprefix tailTrace_600612
  have hstable : (prefixWord ++ tailWord_600612).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600612).length < 2 ^ (prefixWord ++ tailWord_600612).sum := by decide
  have hdescent : baseEnd_600612 < baseStart_600612 := by decide
  rcases family_descends (prefixWord ++ tailWord_600612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600653 : List Nat := [1, 6, 1, 1, 2, 3, 2, 2, 2]
def baseStart_600653 : Nat := 118140960795 + 600653 * 2 ^ 59
def prefixEnd_600653 : Nat := 4983230072969 + 3 ^ 40 * 600653 * 2
def baseEnd_600653 : Nat := 274154396057905489844581

theorem tailTrace_600653 : CollatzResearch.WordTrace tailWord_600653 prefixEnd_600653 274154396057905489844581 := by
  unfold tailWord_600653
  simp only [CollatzResearch.WordTrace]
  refine ⟨21907614692944239210430613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14605076461962826140287075 21907614692944239210430613)
  ·
    refine ⟨1026919438731761212988935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 21907614692944239210430613 1026919438731761212988935)
    ·
      refine ⟨1540379158097641819483403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1026919438731761212988935 1540379158097641819483403)
      ·
        refine ⟨2310568737146462729225105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1540379158097641819483403 2310568737146462729225105)
        ·
          refine ⟨1732926552859847046918829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2310568737146462729225105 1732926552859847046918829)
          ·
            refine ⟨649847457322442642594561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1732926552859847046918829 649847457322442642594561)
            ·
              refine ⟨487385592991831981945921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 649847457322442642594561 487385592991831981945921)
              ·
                refine ⟨365539194743873986459441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 487385592991831981945921 365539194743873986459441)
                ·
                  refine ⟨274154396057905489844581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 365539194743873986459441 274154396057905489844581)
                  ·
                    rfl

theorem cell20_600653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_600653 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_600653 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_600653 prefixEnd_600653 := by exact prefixLift 600653
  have htrace : WordTrace (prefixWord ++ tailWord_600653) baseStart_600653 baseEnd_600653 := by
    simpa [prefixWord, tailWord_600653, baseEnd_600653] using wordTrace_append hprefix tailTrace_600653
  have hstable : (prefixWord ++ tailWord_600653).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600653).length < 2 ^ (prefixWord ++ tailWord_600653).sum := by decide
  have hdescent : baseEnd_600653 < baseStart_600653 := by decide
  rcases family_descends (prefixWord ++ tailWord_600653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600654 : List Nat := [4, 1, 1, 1, 1, 2, 3, 4, 3]
def baseStart_600654 : Nat := 118140960795 + 600654 * 2 ^ 59
def prefixEnd_600654 : Nat := 4983230072969 + 3 ^ 40 * 600654 * 2
def baseEnd_600654 : Nat := 274154852485153930811243

theorem tailTrace_600654 : CollatzResearch.WordTrace tailWord_600654 prefixEnd_600654 274154852485153930811243 := by
  unfold tailWord_600654
  simp only [CollatzResearch.WordTrace]
  refine ⟨2738456395742577047652127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14605100777293744254144677 2738456395742577047652127)
  ·
    refine ⟨4107684593613865571478191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2738456395742577047652127 4107684593613865571478191)
    ·
      refine ⟨6161526890420798357217287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4107684593613865571478191 6161526890420798357217287)
      ·
        refine ⟨9242290335631197535825931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6161526890420798357217287 9242290335631197535825931)
        ·
          refine ⟨13863435503446796303738897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9242290335631197535825931 13863435503446796303738897)
          ·
            refine ⟨10397576627585097227804173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13863435503446796303738897 10397576627585097227804173)
            ·
              refine ⟨3899091235344411460426565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10397576627585097227804173 3899091235344411460426565)
              ·
                refine ⟨731079606627077148829981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3899091235344411460426565 731079606627077148829981)
                ·
                  refine ⟨274154852485153930811243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 731079606627077148829981 274154852485153930811243)
                  ·
                    rfl

theorem cell20_600654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 4, 3].length) (baseStart_600654 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_600654 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_600654 prefixEnd_600654 := by exact prefixLift 600654
  have htrace : WordTrace (prefixWord ++ tailWord_600654) baseStart_600654 baseEnd_600654 := by
    simpa [prefixWord, tailWord_600654, baseEnd_600654] using wordTrace_append hprefix tailTrace_600654
  have hstable : (prefixWord ++ tailWord_600654).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600654).length < 2 ^ (prefixWord ++ tailWord_600654).sum := by decide
  have hdescent : baseEnd_600654 < baseStart_600654 := by decide
  rcases family_descends (prefixWord ++ tailWord_600654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600657 : List Nat := [1, 2, 2, 1, 3, 3, 4, 2, 2]
def baseStart_600657 : Nat := 118140960795 + 600657 * 2 ^ 59
def prefixEnd_600657 : Nat := 4983230072969 + 3 ^ 40 * 600657 * 2
def baseEnd_600657 : Nat := 274156221766899253711231

theorem tailTrace_600657 : CollatzResearch.WordTrace tailWord_600657 prefixEnd_600657 274156221766899253711231 := by
  unfold tailWord_600657
  simp only [CollatzResearch.WordTrace]
  refine ⟨21907760584929747893576225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14605173723286498595717483 21907760584929747893576225)
  ·
    refine ⟨16430820438697310920182169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21907760584929747893576225 16430820438697310920182169)
    ·
      refine ⟨12323115329022983190136627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16430820438697310920182169 12323115329022983190136627)
      ·
        refine ⟨18484672993534474785204941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12323115329022983190136627 18484672993534474785204941)
        ·
          refine ⟨6931752372575428044451853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18484672993534474785204941 6931752372575428044451853)
          ·
            refine ⟨2599407139715785516669445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6931752372575428044451853 2599407139715785516669445)
            ·
              refine ⟨487388838696709784375521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2599407139715785516669445 487388838696709784375521)
              ·
                refine ⟨365541629022532338281641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 487388838696709784375521 365541629022532338281641)
                ·
                  refine ⟨274156221766899253711231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 365541629022532338281641 274156221766899253711231)
                  ·
                    rfl

theorem cell20_600657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 4, 2, 2].length) (baseStart_600657 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_600657 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_600657 prefixEnd_600657 := by exact prefixLift 600657
  have htrace : WordTrace (prefixWord ++ tailWord_600657) baseStart_600657 baseEnd_600657 := by
    simpa [prefixWord, tailWord_600657, baseEnd_600657] using wordTrace_append hprefix tailTrace_600657
  have hstable : (prefixWord ++ tailWord_600657).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600657).length < 2 ^ (prefixWord ++ tailWord_600657).sum := by decide
  have hdescent : baseEnd_600657 < baseStart_600657 := by decide
  rcases family_descends (prefixWord ++ tailWord_600657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600709 : List Nat := [1, 3, 1, 1, 4, 4, 1, 2, 3]
def baseStart_600709 : Nat := 118140960795 + 600709 * 2 ^ 59
def prefixEnd_600709 : Nat := 4983230072969 + 3 ^ 40 * 600709 * 2
def baseEnd_600709 : Nat := 274179955983818183977685

theorem tailTrace_600709 : CollatzResearch.WordTrace tailWord_600709 prefixEnd_600709 274179955983818183977685 := by
  unfold tailWord_600709
  simp only [CollatzResearch.WordTrace]
  refine ⟨21909657180741360774469181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14606438120494240516312787 21909657180741360774469181)
  ·
    refine ⟨8216121442778010290425943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21909657180741360774469181 8216121442778010290425943)
    ·
      refine ⟨12324182164167015435638915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8216121442778010290425943 12324182164167015435638915)
      ·
        refine ⟨18486273246250523153458373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12324182164167015435638915 18486273246250523153458373)
        ·
          refine ⟨3466176233671973091273445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18486273246250523153458373 3466176233671973091273445)
          ·
            refine ⟨649908043813494954613771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3466176233671973091273445 649908043813494954613771)
            ·
              refine ⟨974862065720242431920657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 649908043813494954613771 974862065720242431920657)
              ·
                refine ⟨731146549290181823940493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 974862065720242431920657 731146549290181823940493)
                ·
                  refine ⟨274179955983818183977685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 731146549290181823940493 274179955983818183977685)
                  ·
                    rfl

theorem cell20_600709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 2, 3].length) (baseStart_600709 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_600709 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_600709 prefixEnd_600709 := by exact prefixLift 600709
  have htrace : WordTrace (prefixWord ++ tailWord_600709) baseStart_600709 baseEnd_600709 := by
    simpa [prefixWord, tailWord_600709, baseEnd_600709] using wordTrace_append hprefix tailTrace_600709
  have hstable : (prefixWord ++ tailWord_600709).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600709).length < 2 ^ (prefixWord ++ tailWord_600709).sum := by decide
  have hdescent : baseEnd_600709 < baseStart_600709 := by decide
  rcases family_descends (prefixWord ++ tailWord_600709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600746 : List Nat := [3, 1, 5, 2, 2, 1, 1, 3, 2]
def baseStart_600746 : Nat := 118140960795 + 600746 * 2 ^ 59
def prefixEnd_600746 : Nat := 4983230072969 + 3 ^ 40 * 600746 * 2
def baseEnd_600746 : Nat := 274196843792010499744201

theorem tailTrace_600746 : CollatzResearch.WordTrace tailWord_600746 prefixEnd_600746 274196843792010499744201 := by
  unfold tailWord_600746
  simp only [CollatzResearch.WordTrace]
  refine ⟨5477751670401829023391523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14607337787738210729044061 5477751670401829023391523)
  ·
    refine ⟨8216627505602743535087285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5477751670401829023391523 8216627505602743535087285)
    ·
      refine ⟨770308828650257206414433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8216627505602743535087285 770308828650257206414433)
      ·
        refine ⟨577731621487692904810825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 770308828650257206414433 577731621487692904810825)
        ·
          refine ⟨433298716115769678608119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 577731621487692904810825 433298716115769678608119)
          ·
            refine ⟨649948074173654517912179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 433298716115769678608119 649948074173654517912179)
            ·
              refine ⟨974922111260481776868269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 649948074173654517912179 974922111260481776868269)
              ·
                refine ⟨365595791722680666325601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 974922111260481776868269 365595791722680666325601)
                ·
                  refine ⟨274196843792010499744201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 365595791722680666325601 274196843792010499744201)
                  ·
                    rfl

theorem cell20_600746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 3, 2].length) (baseStart_600746 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_600746 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_600746 prefixEnd_600746 := by exact prefixLift 600746
  have htrace : WordTrace (prefixWord ++ tailWord_600746) baseStart_600746 baseEnd_600746 := by
    simpa [prefixWord, tailWord_600746, baseEnd_600746] using wordTrace_append hprefix tailTrace_600746
  have hstable : (prefixWord ++ tailWord_600746).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600746).length < 2 ^ (prefixWord ++ tailWord_600746).sum := by decide
  have hdescent : baseEnd_600746 < baseStart_600746 := by decide
  rcases family_descends (prefixWord ++ tailWord_600746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600750 : List Nat := [4, 1, 4, 1, 1, 1, 3, 3, 2]
def baseStart_600750 : Nat := 118140960795 + 600750 * 2 ^ 59
def prefixEnd_600750 : Nat := 4983230072969 + 3 ^ 40 * 600750 * 2
def baseEnd_600750 : Nat := 274198669501004263610851

theorem tailTrace_600750 : CollatzResearch.WordTrace tailWord_600750 prefixEnd_600750 274198669501004263610851 := by
  unfold tailWord_600750
  simp only [CollatzResearch.WordTrace]
  refine ⟨2738894071699103097088963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14607435049061883184474469 2738894071699103097088963)
  ·
    refine ⟨4108341107548654645633445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2738894071699103097088963 4108341107548654645633445)
    ·
      refine ⟨770313957665372746056271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4108341107548654645633445 770313957665372746056271)
      ·
        refine ⟨1155470936498059119084407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 770313957665372746056271 1155470936498059119084407)
        ·
          refine ⟨1733206404747088678626611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1155470936498059119084407 1733206404747088678626611)
          ·
            refine ⟨2599809607120633017939917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1733206404747088678626611 2599809607120633017939917)
            ·
              refine ⟨974928602670237381727469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2599809607120633017939917 974928602670237381727469)
              ·
                refine ⟨365598226001339018147801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 974928602670237381727469 365598226001339018147801)
                ·
                  refine ⟨274198669501004263610851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 365598226001339018147801 274198669501004263610851)
                  ·
                    rfl

theorem cell20_600750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 3, 2].length) (baseStart_600750 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_600750 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_600750 prefixEnd_600750 := by exact prefixLift 600750
  have htrace : WordTrace (prefixWord ++ tailWord_600750) baseStart_600750 baseEnd_600750 := by
    simpa [prefixWord, tailWord_600750, baseEnd_600750] using wordTrace_append hprefix tailTrace_600750
  have hstable : (prefixWord ++ tailWord_600750).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600750).length < 2 ^ (prefixWord ++ tailWord_600750).sum := by decide
  have hdescent : baseEnd_600750 < baseStart_600750 := by decide
  rcases family_descends (prefixWord ++ tailWord_600750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600751 : List Nat := [1, 1, 2, 1, 2, 5, 1, 2, 5]
def baseStart_600751 : Nat := 118140960795 + 600751 * 2 ^ 59
def prefixEnd_600751 : Nat := 4983230072969 + 3 ^ 40 * 600751 * 2
def baseEnd_600751 : Nat := 274199125928252704577513

theorem tailTrace_600751 : CollatzResearch.WordTrace tailWord_600751 prefixEnd_600751 274199125928252704577513 := by
  unfold tailWord_600751
  simp only [CollatzResearch.WordTrace]
  refine ⟨21911189046589201947498107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14607459364392801298332071 21911189046589201947498107)
  ·
    refine ⟨32866783569883802921247161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21911189046589201947498107 32866783569883802921247161)
    ·
      refine ⟨24650087677412852190935371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32866783569883802921247161 24650087677412852190935371)
      ·
        refine ⟨36975131516119278286403057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24650087677412852190935371 36975131516119278286403057)
        ·
          refine ⟨27731348637089458714802293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36975131516119278286403057 27731348637089458714802293)
          ·
            refine ⟨2599813934727136754512715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27731348637089458714802293 2599813934727136754512715)
            ·
              refine ⟨3899720902090705131769073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2599813934727136754512715 3899720902090705131769073)
              ·
                refine ⟨2924790676568028848826805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3899720902090705131769073 2924790676568028848826805)
                ·
                  refine ⟨274199125928252704577513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2924790676568028848826805 274199125928252704577513)
                  ·
                    rfl

theorem cell20_600751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 5].length) (baseStart_600751 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_600751 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_600751 prefixEnd_600751 := by exact prefixLift 600751
  have htrace : WordTrace (prefixWord ++ tailWord_600751) baseStart_600751 baseEnd_600751 := by
    simpa [prefixWord, tailWord_600751, baseEnd_600751] using wordTrace_append hprefix tailTrace_600751
  have hstable : (prefixWord ++ tailWord_600751).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600751).length < 2 ^ (prefixWord ++ tailWord_600751).sum := by decide
  have hdescent : baseEnd_600751 < baseStart_600751 := by decide
  rcases family_descends (prefixWord ++ tailWord_600751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600782 : List Nat := [4, 1, 1, 1, 3, 2, 1, 7]
def baseStart_600782 : Nat := 118140960795 + 600782 * 2 ^ 59
def prefixEnd_600782 : Nat := 4983230072969 + 3 ^ 40 * 600782 * 2
def baseEnd_600782 : Nat := 91404425057651458181351

theorem tailTrace_600782 : CollatzResearch.WordTrace tailWord_600782 prefixEnd_600782 91404425057651458181351 := by
  unfold tailWord_600782
  simp only [CollatzResearch.WordTrace]
  refine ⟨2739039963684611780234575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14608213139651262827917733 2739039963684611780234575)
  ·
    refine ⟨4108559945526917670351863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2739039963684611780234575 4108559945526917670351863)
    ·
      refine ⟨6162839918290376505527795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4108559945526917670351863 6162839918290376505527795)
      ·
        refine ⟨9244259877435564758291693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6162839918290376505527795 9244259877435564758291693)
        ·
          refine ⟨3466597454038336784359385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9244259877435564758291693 3466597454038336784359385)
          ·
            refine ⟨2599948090528752588269539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3466597454038336784359385 2599948090528752588269539)
            ·
              refine ⟨3899922135793128882404309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2599948090528752588269539 3899922135793128882404309)
              ·
                refine ⟨91404425057651458181351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3899922135793128882404309 91404425057651458181351)
                ·
                  rfl

theorem cell20_600782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_600782 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_600782 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_600782 prefixEnd_600782 := by exact prefixLift 600782
  have htrace : WordTrace (prefixWord ++ tailWord_600782) baseStart_600782 baseEnd_600782 := by
    simpa [prefixWord, tailWord_600782, baseEnd_600782] using wordTrace_append hprefix tailTrace_600782
  have hstable : (prefixWord ++ tailWord_600782).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600782).length < 2 ^ (prefixWord ++ tailWord_600782).sum := by decide
  have hdescent : baseEnd_600782 < baseStart_600782 := by decide
  rcases family_descends (prefixWord ++ tailWord_600782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600865 : List Nat := [1, 2, 3, 2, 1, 2, 2, 2, 5]
def baseStart_600865 : Nat := 118140960795 + 600865 * 2 ^ 59
def prefixEnd_600865 : Nat := 4983230072969 + 3 ^ 40 * 600865 * 2
def baseEnd_600865 : Nat := 274251158634574974777047

theorem tailTrace_600865 : CollatzResearch.WordTrace tailWord_600865 prefixEnd_600865 274251158634574974777047 := by
  unfold tailWord_600865
  simp only [CollatzResearch.WordTrace]
  refine ⟨21915346968176199417148049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14610231312117466278098699 21915346968176199417148049)
  ·
    refine ⟨16436510226132149562861037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21915346968176199417148049 16436510226132149562861037)
    ·
      refine ⟨6163691334799556086072889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16436510226132149562861037 6163691334799556086072889)
      ·
        refine ⟨4622768501099667064554667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6163691334799556086072889 4622768501099667064554667)
        ·
          refine ⟨6934152751649500596832001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4622768501099667064554667 6934152751649500596832001)
          ·
            refine ⟨5200614563737125447624001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6934152751649500596832001 5200614563737125447624001)
            ·
              refine ⟨3900460922802844085718001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5200614563737125447624001 3900460922802844085718001)
              ·
                refine ⟨2925345692102133064288501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3900460922802844085718001 2925345692102133064288501)
                ·
                  refine ⟨274251158634574974777047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2925345692102133064288501 274251158634574974777047)
                  ·
                    rfl

theorem cell20_600865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 5].length) (baseStart_600865 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_600865 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_600865 prefixEnd_600865 := by exact prefixLift 600865
  have htrace : WordTrace (prefixWord ++ tailWord_600865) baseStart_600865 baseEnd_600865 := by
    simpa [prefixWord, tailWord_600865, baseEnd_600865] using wordTrace_append hprefix tailTrace_600865
  have hstable : (prefixWord ++ tailWord_600865).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600865).length < 2 ^ (prefixWord ++ tailWord_600865).sum := by decide
  have hdescent : baseEnd_600865 < baseStart_600865 := by decide
  rcases family_descends (prefixWord ++ tailWord_600865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600878 : List Nat := [4, 1, 3, 2, 1, 3, 1, 2, 3]
def baseStart_600878 : Nat := 118140960795 + 600878 * 2 ^ 59
def prefixEnd_600878 : Nat := 4983230072969 + 3 ^ 40 * 600878 * 2
def baseEnd_600878 : Nat := 274257092188804707343661

theorem tailTrace_600878 : CollatzResearch.WordTrace tailWord_600878 prefixEnd_600878 274257092188804707343661 := by
  unfold tailWord_600878
  simp only [CollatzResearch.WordTrace]
  refine ⟨2739477639641137829671411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14610547411419401758247525 2739477639641137829671411)
  ·
    refine ⟨4109216459461706744507117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2739477639641137829671411 4109216459461706744507117)
    ·
      refine ⟨1540956172298140029190169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4109216459461706744507117 1540956172298140029190169)
      ·
        refine ⟨1155717129223605021892627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1540956172298140029190169 1155717129223605021892627)
        ·
          refine ⟨1733575693835407532838941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1155717129223605021892627 1733575693835407532838941)
          ·
            refine ⟨650090885188277824814603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1733575693835407532838941 650090885188277824814603)
            ·
              refine ⟨975136327782416737221905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 650090885188277824814603 975136327782416737221905)
              ·
                refine ⟨731352245836812552916429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 975136327782416737221905 731352245836812552916429)
                ·
                  refine ⟨274257092188804707343661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 731352245836812552916429 274257092188804707343661)
                  ·
                    rfl

theorem cell20_600878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 2, 3].length) (baseStart_600878 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_600878 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_600878 prefixEnd_600878 := by exact prefixLift 600878
  have htrace : WordTrace (prefixWord ++ tailWord_600878) baseStart_600878 baseEnd_600878 := by
    simpa [prefixWord, tailWord_600878, baseEnd_600878] using wordTrace_append hprefix tailTrace_600878
  have hstable : (prefixWord ++ tailWord_600878).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600878).length < 2 ^ (prefixWord ++ tailWord_600878).sum := by decide
  have hdescent : baseEnd_600878 < baseStart_600878 := by decide
  rcases family_descends (prefixWord ++ tailWord_600878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600909 : List Nat := [1, 6, 1, 2, 2, 2, 2, 4]
def baseStart_600909 : Nat := 118140960795 + 600909 * 2 ^ 59
def prefixEnd_600909 : Nat := 4983230072969 + 3 ^ 40 * 600909 * 2
def baseEnd_600909 : Nat := 91423747144502125770067

theorem tailTrace_600909 : CollatzResearch.WordTrace tailWord_600909 prefixEnd_600909 91423747144502125770067 := by
  unfold tailWord_600909
  simp only [CollatzResearch.WordTrace]
  refine ⟨21916951780016794931749781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14611301186677863287833187 21916951780016794931749781)
  ·
    refine ⟨1027357114688287262425771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 21916951780016794931749781 1027357114688287262425771)
    ·
      refine ⟨1541035672032430893638657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1027357114688287262425771 1541035672032430893638657)
      ·
        refine ⟨1155776754024323170228993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1541035672032430893638657 1155776754024323170228993)
        ·
          refine ⟨866832565518242377671745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1155776754024323170228993 866832565518242377671745)
          ·
            refine ⟨650124424138681783253809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 866832565518242377671745 650124424138681783253809)
            ·
              refine ⟨487593318104011337440357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 650124424138681783253809 487593318104011337440357)
              ·
                refine ⟨91423747144502125770067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 487593318104011337440357 91423747144502125770067)
                ·
                  rfl

theorem cell20_600909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 2, 4].length) (baseStart_600909 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_600909 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_600909 prefixEnd_600909 := by exact prefixLift 600909
  have htrace : WordTrace (prefixWord ++ tailWord_600909) baseStart_600909 baseEnd_600909 := by
    simpa [prefixWord, tailWord_600909, baseEnd_600909] using wordTrace_append hprefix tailTrace_600909
  have hstable : (prefixWord ++ tailWord_600909).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600909).length < 2 ^ (prefixWord ++ tailWord_600909).sum := by decide
  have hdescent : baseEnd_600909 < baseStart_600909 := by decide
  rcases family_descends (prefixWord ++ tailWord_600909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600930 : List Nat := [3, 3, 2, 1, 4, 1, 6]
def baseStart_600930 : Nat := 118140960795 + 600930 * 2 ^ 59
def prefixEnd_600930 : Nat := 4983230072969 + 3 ^ 40 * 600930 * 2
def baseEnd_600930 : Nat := 30475647378413737512235

theorem tailTrace_600930 : CollatzResearch.WordTrace tailWord_600930 prefixEnd_600930 30475647378413737512235 := by
  unfold tailWord_600930
  simp only [CollatzResearch.WordTrace]
  refine ⟨5479429428235178879566061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14611811808627143678842829 5479429428235178879566061)
  ·
    refine ⟨2054786035588192079837273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5479429428235178879566061 2054786035588192079837273)
    ·
      refine ⟨1541089526691144059877955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2054786035588192079837273 1541089526691144059877955)
      ·
        refine ⟨2311634290036716089816933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1541089526691144059877955 2311634290036716089816933)
        ·
          refine ⟨433431429381884266840675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2311634290036716089816933 433431429381884266840675)
          ·
            refine ⟨650147144072826400261013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 433431429381884266840675 650147144072826400261013)
            ·
              refine ⟨30475647378413737512235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 650147144072826400261013 30475647378413737512235)
              ·
                rfl

theorem cell20_600930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 6].length) (baseStart_600930 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_600930 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_600930 prefixEnd_600930 := by exact prefixLift 600930
  have htrace : WordTrace (prefixWord ++ tailWord_600930) baseStart_600930 baseEnd_600930 := by
    simpa [prefixWord, tailWord_600930, baseEnd_600930] using wordTrace_append hprefix tailTrace_600930
  have hstable : (prefixWord ++ tailWord_600930).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600930).length < 2 ^ (prefixWord ++ tailWord_600930).sum := by decide
  have hdescent : baseEnd_600930 < baseStart_600930 := by decide
  rcases family_descends (prefixWord ++ tailWord_600930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600955 : List Nat := [1, 1, 1, 1, 1, 5, 3, 7]
def baseStart_600955 : Nat := 118140960795 + 600955 * 2 ^ 59
def prefixEnd_600955 : Nat := 4983230072969 + 3 ^ 40 * 600955 * 2
def baseEnd_600955 : Nat := 91430745695644887258893

theorem tailTrace_600955 : CollatzResearch.WordTrace tailWord_600955 prefixEnd_600955 91430745695644887258893 := by
  unfold tailWord_600955
  simp only [CollatzResearch.WordTrace]
  refine ⟨21918629537850144787924319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14612419691900096525282879 21918629537850144787924319)
  ·
    refine ⟨32877944306775217181886479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21918629537850144787924319 32877944306775217181886479)
    ·
      refine ⟨49316916460162825772829719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32877944306775217181886479 49316916460162825772829719)
      ·
        refine ⟨73975374690244238659244579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49316916460162825772829719 73975374690244238659244579)
        ·
          refine ⟨110963062035366357988866869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73975374690244238659244579 110963062035366357988866869)
          ·
            refine ⟨10402787065815596061456269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 110963062035366357988866869 10402787065815596061456269)
            ·
              refine ⟨3901045149680848523046101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10402787065815596061456269 3901045149680848523046101)
              ·
                refine ⟨91430745695644887258893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3901045149680848523046101 91430745695644887258893)
                ·
                  rfl

theorem cell20_600955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 7].length) (baseStart_600955 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_600955 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_600955 prefixEnd_600955 := by exact prefixLift 600955
  have htrace : WordTrace (prefixWord ++ tailWord_600955) baseStart_600955 baseEnd_600955 := by
    simpa [prefixWord, tailWord_600955, baseEnd_600955] using wordTrace_append hprefix tailTrace_600955
  have hstable : (prefixWord ++ tailWord_600955).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600955).length < 2 ^ (prefixWord ++ tailWord_600955).sum := by decide
  have hdescent : baseEnd_600955 < baseStart_600955 := by decide
  rcases family_descends (prefixWord ++ tailWord_600955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600996 : List Nat := [2, 3, 1, 2, 1, 2, 4, 2, 3]
def baseStart_600996 : Nat := 118140960795 + 600996 * 2 ^ 59
def prefixEnd_600996 : Nat := 4983230072969 + 3 ^ 40 * 600996 * 2
def baseEnd_600996 : Nat := 274310950604120741409845

theorem tailTrace_600996 : CollatzResearch.WordTrace tailWord_600996 prefixEnd_600996 274310950604120741409845 := by
  unfold tailWord_600996
  simp only [CollatzResearch.WordTrace]
  refine ⟨10960062465350804395083421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14613416620467739193444561 10960062465350804395083421)
  ·
    refine ⟨4110023424506551648156283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10960062465350804395083421 4110023424506551648156283)
    ·
      refine ⟨6165035136759827472234425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4110023424506551648156283 6165035136759827472234425)
      ·
        refine ⟨4623776352569870604175819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6165035136759827472234425 4623776352569870604175819)
        ·
          refine ⟨6935664528854805906263729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4623776352569870604175819 6935664528854805906263729)
          ·
            refine ⟨5201748396641104429697797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6935664528854805906263729 5201748396641104429697797)
            ·
              refine ⟨975327824370207080568337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5201748396641104429697797 975327824370207080568337)
              ·
                refine ⟨731495868277655310426253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 975327824370207080568337 731495868277655310426253)
                ·
                  refine ⟨274310950604120741409845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 731495868277655310426253 274310950604120741409845)
                  ·
                    rfl

theorem cell20_600996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 2, 3].length) (baseStart_600996 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_600996 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_600996 prefixEnd_600996 := by exact prefixLift 600996
  have htrace : WordTrace (prefixWord ++ tailWord_600996) baseStart_600996 baseEnd_600996 := by
    simpa [prefixWord, tailWord_600996, baseEnd_600996] using wordTrace_append hprefix tailTrace_600996
  have hstable : (prefixWord ++ tailWord_600996).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600996).length < 2 ^ (prefixWord ++ tailWord_600996).sum := by decide
  have hdescent : baseEnd_600996 < baseStart_600996 := by decide
  rcases family_descends (prefixWord ++ tailWord_600996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600999 : List Nat := [1, 1, 6, 1, 3, 1, 1, 4, 2]
def baseStart_600999 : Nat := 118140960795 + 600999 * 2 ^ 59
def prefixEnd_600999 : Nat := 4983230072969 + 3 ^ 40 * 600999 * 2
def baseEnd_600999 : Nat := 274312319885866064309833

theorem tailTrace_600999 : CollatzResearch.WordTrace tailWord_600999 prefixEnd_600999 274312319885866064309833 := by
  unfold tailWord_600999
  simp only [CollatzResearch.WordTrace]
  refine ⟨21920234349690740302526051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14613489566460493535017367 21920234349690740302526051)
  ·
    refine ⟨32880351524536110453789077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21920234349690740302526051 32880351524536110453789077)
    ·
      refine ⟨1541266477712630177521363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 32880351524536110453789077 1541266477712630177521363)
      ·
        refine ⟨2311899716568945266282045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1541266477712630177521363 2311899716568945266282045)
        ·
          refine ⟨866962393713354474855767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2311899716568945266282045 866962393713354474855767)
          ·
            refine ⟨1300443590570031712283651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 866962393713354474855767 1300443590570031712283651)
            ·
              refine ⟨1950665385855047568425477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1300443590570031712283651 1950665385855047568425477)
              ·
                refine ⟨365749759847821419079777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1950665385855047568425477 365749759847821419079777)
                ·
                  refine ⟨274312319885866064309833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 365749759847821419079777 274312319885866064309833)
                  ·
                    rfl

theorem cell20_600999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 4, 2].length) (baseStart_600999 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_600999 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_600999 prefixEnd_600999 := by exact prefixLift 600999
  have htrace : WordTrace (prefixWord ++ tailWord_600999) baseStart_600999 baseEnd_600999 := by
    simpa [prefixWord, tailWord_600999, baseEnd_600999] using wordTrace_append hprefix tailTrace_600999
  have hstable : (prefixWord ++ tailWord_600999).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600999).length < 2 ^ (prefixWord ++ tailWord_600999).sum := by decide
  have hdescent : baseEnd_600999 < baseStart_600999 := by decide
  rcases family_descends (prefixWord ++ tailWord_600999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601003 : List Nat := [1, 1, 1, 1, 2, 1, 1, 10, 2]
def baseStart_601003 : Nat := 118140960795 + 601003 * 2 ^ 59
def prefixEnd_601003 : Nat := 4983230072969 + 3 ^ 40 * 601003 * 2
def baseEnd_601003 : Nat := 274314145594859828176483

theorem tailTrace_601003 : CollatzResearch.WordTrace tailWord_601003 prefixEnd_601003 274314145594859828176483 := by
  unfold tailWord_601003
  simp only [CollatzResearch.WordTrace]
  refine ⟨21920380241676248985671663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14613586827784165990447775 21920380241676248985671663)
  ·
    refine ⟨32880570362514373478507495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21920380241676248985671663 32880570362514373478507495)
    ·
      refine ⟨49320855543771560217761243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32880570362514373478507495 49320855543771560217761243)
      ·
        refine ⟨73981283315657340326641865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49320855543771560217761243 73981283315657340326641865)
        ·
          refine ⟨55485962486743005244981399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73981283315657340326641865 55485962486743005244981399)
          ·
            refine ⟨83228943730114507867472099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55485962486743005244981399 83228943730114507867472099)
            ·
              refine ⟨124843415595171761801208149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83228943730114507867472099 124843415595171761801208149)
              ·
                refine ⟨365752194126479770901977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 124843415595171761801208149 365752194126479770901977)
                ·
                  refine ⟨274314145594859828176483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 365752194126479770901977 274314145594859828176483)
                  ·
                    rfl

theorem cell20_601003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 10, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 10, 2].length) (baseStart_601003 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_601003 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_601003 prefixEnd_601003 := by exact prefixLift 601003
  have htrace : WordTrace (prefixWord ++ tailWord_601003) baseStart_601003 baseEnd_601003 := by
    simpa [prefixWord, tailWord_601003, baseEnd_601003] using wordTrace_append hprefix tailTrace_601003
  have hstable : (prefixWord ++ tailWord_601003).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601003).length < 2 ^ (prefixWord ++ tailWord_601003).sum := by decide
  have hdescent : baseEnd_601003 < baseStart_601003 := by decide
  rcases family_descends (prefixWord ++ tailWord_601003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601024 : List Nat := [2, 1, 1, 2, 3, 3, 1, 1, 6]
def baseStart_601024 : Nat := 118140960795 + 601024 * 2 ^ 59
def prefixEnd_601024 : Nat := 4983230072969 + 3 ^ 40 * 601024 * 2
def baseEnd_601024 : Nat := 274323730567077088476397

theorem tailTrace_601024 : CollatzResearch.WordTrace tailWord_601024 prefixEnd_601024 274323730567077088476397 := by
  unfold tailWord_601024
  simp only [CollatzResearch.WordTrace]
  refine ⟨10960573087300084786093063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14614097449733446381457417 10960573087300084786093063)
  ·
    refine ⟨16440859630950127179139595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10960573087300084786093063 16440859630950127179139595)
    ·
      refine ⟨24661289446425190768709393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16440859630950127179139595 24661289446425190768709393)
      ·
        refine ⟨18495967084818893076532045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24661289446425190768709393 18495967084818893076532045)
        ·
          refine ⟨6935987656807084903699517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18495967084818893076532045 6935987656807084903699517)
          ·
            refine ⟨2600995371302656838887319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6935987656807084903699517 2600995371302656838887319)
            ·
              refine ⟨3901493056953985258330979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2600995371302656838887319 3901493056953985258330979)
              ·
                refine ⟨5852239585430977887496469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3901493056953985258330979 5852239585430977887496469)
                ·
                  refine ⟨274323730567077088476397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5852239585430977887496469 274323730567077088476397)
                  ·
                    rfl

theorem cell20_601024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 6].length) (baseStart_601024 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_601024 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_601024 prefixEnd_601024 := by exact prefixLift 601024
  have htrace : WordTrace (prefixWord ++ tailWord_601024) baseStart_601024 baseEnd_601024 := by
    simpa [prefixWord, tailWord_601024, baseEnd_601024] using wordTrace_append hprefix tailTrace_601024
  have hstable : (prefixWord ++ tailWord_601024).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601024).length < 2 ^ (prefixWord ++ tailWord_601024).sum := by decide
  have hdescent : baseEnd_601024 < baseStart_601024 := by decide
  rcases family_descends (prefixWord ++ tailWord_601024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601031 : List Nat := [1, 1, 4, 1, 1, 2, 2, 8]
def baseStart_601031 : Nat := 118140960795 + 601031 * 2 ^ 59
def prefixEnd_601031 : Nat := 4983230072969 + 3 ^ 40 * 601031 * 2
def baseEnd_601031 : Nat := 91442308519272058414345

theorem tailTrace_601031 : CollatzResearch.WordTrace tailWord_601031 prefixEnd_601031 91442308519272058414345 := by
  unfold tailWord_601031
  simp only [CollatzResearch.WordTrace]
  refine ⟨21921401485574809767690947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14614267657049873178460631 21921401485574809767690947)
  ·
    refine ⟨32882102228362214651536421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21921401485574809767690947 32882102228362214651536421)
    ·
      refine ⟨6165394167817915247163079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32882102228362214651536421 6165394167817915247163079)
      ·
        refine ⟨9248091251726872870744619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6165394167817915247163079 9248091251726872870744619)
        ·
          refine ⟨13872136877590309306116929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9248091251726872870744619 13872136877590309306116929)
          ·
            refine ⟨10404102658192731979587697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13872136877590309306116929 10404102658192731979587697)
            ·
              refine ⟨7803076993644548984690773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10404102658192731979587697 7803076993644548984690773)
              ·
                refine ⟨91442308519272058414345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7803076993644548984690773 91442308519272058414345)
                ·
                  rfl

theorem cell20_601031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 8].length) (baseStart_601031 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_601031 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_601031 prefixEnd_601031 := by exact prefixLift 601031
  have htrace : WordTrace (prefixWord ++ tailWord_601031) baseStart_601031 baseEnd_601031 := by
    simpa [prefixWord, tailWord_601031, baseEnd_601031] using wordTrace_append hprefix tailTrace_601031
  have hstable : (prefixWord ++ tailWord_601031).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601031).length < 2 ^ (prefixWord ++ tailWord_601031).sum := by decide
  have hdescent : baseEnd_601031 < baseStart_601031 := by decide
  rcases family_descends (prefixWord ++ tailWord_601031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601058 : List Nat := [3, 3, 3, 1, 1, 1, 1, 3, 4]
def baseStart_601058 : Nat := 118140960795 + 601058 * 2 ^ 59
def prefixEnd_601058 : Nat := 4983230072969 + 3 ^ 40 * 601058 * 2
def baseEnd_601058 : Nat := 274339249093524081342925

theorem tailTrace_601058 : CollatzResearch.WordTrace tailWord_601058 prefixEnd_601058 274339249093524081342925 := by
  unfold tailWord_601058
  simp only [CollatzResearch.WordTrace]
  refine ⟨5480596564119248344730957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14614924170984662252615885 5480596564119248344730957)
  ·
    refine ⟨2055223711544718129274109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5480596564119248344730957 2055223711544718129274109)
    ·
      refine ⟨770708891829269298477791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2055223711544718129274109 770708891829269298477791)
      ·
        refine ⟨1156063337743903947716687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 770708891829269298477791 1156063337743903947716687)
        ·
          refine ⟨1734095006615855921575031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1156063337743903947716687 1734095006615855921575031)
          ·
            refine ⟨2601142509923783882362547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1734095006615855921575031 2601142509923783882362547)
            ·
              refine ⟨3901713764885675823543821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2601142509923783882362547 3901713764885675823543821)
              ·
                refine ⟨1463142661832128433828933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3901713764885675823543821 1463142661832128433828933)
                ·
                  refine ⟨274339249093524081342925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1463142661832128433828933 274339249093524081342925)
                  ·
                    rfl

theorem cell20_601058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_601058 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_601058 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_601058 prefixEnd_601058 := by exact prefixLift 601058
  have htrace : WordTrace (prefixWord ++ tailWord_601058) baseStart_601058 baseEnd_601058 := by
    simpa [prefixWord, tailWord_601058, baseEnd_601058] using wordTrace_append hprefix tailTrace_601058
  have hstable : (prefixWord ++ tailWord_601058).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601058).length < 2 ^ (prefixWord ++ tailWord_601058).sum := by decide
  have hdescent : baseEnd_601058 < baseStart_601058 := by decide
  rcases family_descends (prefixWord ++ tailWord_601058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601096 : List Nat := [2, 1, 3, 2, 1, 3, 3, 3, 2]
def baseStart_601096 : Nat := 118140960795 + 601096 * 2 ^ 59
def prefixEnd_601096 : Nat := 4983230072969 + 3 ^ 40 * 601096 * 2
def baseEnd_601096 : Nat := 274356593328964838076103

theorem tailTrace_601096 : CollatzResearch.WordTrace tailWord_601096 prefixEnd_601096 274356593328964838076103 := by
  unfold tailWord_601096
  simp only [CollatzResearch.WordTrace]
  refine ⟨10961886115169662934403571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14615848153559550579204761 10961886115169662934403571)
  ·
    refine ⟨16442829172754494401605357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10961886115169662934403571 16442829172754494401605357)
    ·
      refine ⟨6166060939782935400602009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16442829172754494401605357 6166060939782935400602009)
      ·
        refine ⟨4624545704837201550451507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6166060939782935400602009 4624545704837201550451507)
        ·
          refine ⟨6936818557255802325677261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4624545704837201550451507 6936818557255802325677261)
          ·
            refine ⟨2601306958970925872128973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6936818557255802325677261 2601306958970925872128973)
            ·
              refine ⟨975490109614097202048365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2601306958970925872128973 975490109614097202048365)
              ·
                refine ⟨365808791105286450768137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 975490109614097202048365 365808791105286450768137)
                ·
                  refine ⟨274356593328964838076103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 365808791105286450768137 274356593328964838076103)
                  ·
                    rfl

theorem cell20_601096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 3, 2].length) (baseStart_601096 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_601096 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_601096 prefixEnd_601096 := by exact prefixLift 601096
  have htrace : WordTrace (prefixWord ++ tailWord_601096) baseStart_601096 baseEnd_601096 := by
    simpa [prefixWord, tailWord_601096, baseEnd_601096] using wordTrace_append hprefix tailTrace_601096
  have hstable : (prefixWord ++ tailWord_601096).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601096).length < 2 ^ (prefixWord ++ tailWord_601096).sum := by decide
  have hdescent : baseEnd_601096 < baseStart_601096 := by decide
  rcases family_descends (prefixWord ++ tailWord_601096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601124 : List Nat := [2, 3, 1, 4, 1, 1, 1, 7]
def baseStart_601124 : Nat := 118140960795 + 601124 * 2 ^ 59
def prefixEnd_601124 : Nat := 4983230072969 + 3 ^ 40 * 601124 * 2
def baseEnd_601124 : Nat := 91456457763973728380885

theorem tailTrace_601124 : CollatzResearch.WordTrace tailWord_601124 prefixEnd_601124 91456457763973728380885 := by
  unfold tailWord_601124
  simp only [CollatzResearch.WordTrace]
  refine ⟨10962396737118943325413213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14616528982825257767217617 10962396737118943325413213)
  ·
    refine ⟨4110898776419603747029955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10962396737118943325413213 4110898776419603747029955)
    ·
      refine ⟨6166348164629405620544933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4110898776419603747029955 6166348164629405620544933)
      ·
        refine ⟨1156190280868013553852175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6166348164629405620544933 1156190280868013553852175)
        ·
          refine ⟨1734285421302020330778263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1156190280868013553852175 1734285421302020330778263)
          ·
            refine ⟨2601428131953030496167395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1734285421302020330778263 2601428131953030496167395)
            ·
              refine ⟨3902142197929545744251093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2601428131953030496167395 3902142197929545744251093)
              ·
                refine ⟨91456457763973728380885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3902142197929545744251093 91456457763973728380885)
                ·
                  rfl

theorem cell20_601124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 7].length) (baseStart_601124 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_601124 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_601124 prefixEnd_601124 := by exact prefixLift 601124
  have htrace : WordTrace (prefixWord ++ tailWord_601124) baseStart_601124 baseEnd_601124 := by
    simpa [prefixWord, tailWord_601124, baseEnd_601124] using wordTrace_append hprefix tailTrace_601124
  have hstable : (prefixWord ++ tailWord_601124).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601124).length < 2 ^ (prefixWord ++ tailWord_601124).sum := by decide
  have hdescent : baseEnd_601124 < baseStart_601124 := by decide
  rcases family_descends (prefixWord ++ tailWord_601124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601127 : List Nat := [1, 1, 7, 1, 1, 2, 1, 3, 3]
def baseStart_601127 : Nat := 118140960795 + 601127 * 2 ^ 59
def prefixEnd_601127 : Nat := 4983230072969 + 3 ^ 40 * 601127 * 2
def baseEnd_601127 : Nat := 274370742573666508042643

theorem tailTrace_601127 : CollatzResearch.WordTrace tailWord_601127 prefixEnd_601127 274370742573666508042643 := by
  unfold tailWord_601127
  simp only [CollatzResearch.WordTrace]
  refine ⟨21924902893227018163185635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14616601928818012108790423 21924902893227018163185635)
  ·
    refine ⟨32887354339840527244778453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21924902893227018163185635 32887354339840527244778453)
    ·
      refine ⟨770797367340012357299495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 32887354339840527244778453 770797367340012357299495)
      ·
        refine ⟨1156196051010018535949243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 770797367340012357299495 1156196051010018535949243)
        ·
          refine ⟨1734294076515027803923865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1156196051010018535949243 1734294076515027803923865)
          ·
            refine ⟨1300720557386270852942899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1734294076515027803923865 1300720557386270852942899)
            ·
              refine ⟨1951080836079406279414349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1300720557386270852942899 1951080836079406279414349)
              ·
                refine ⟨731655313529777354780381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1951080836079406279414349 731655313529777354780381)
                ·
                  refine ⟨274370742573666508042643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 731655313529777354780381 274370742573666508042643)
                  ·
                    rfl

theorem cell20_601127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 3, 3].length) (baseStart_601127 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_601127 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_601127 prefixEnd_601127 := by exact prefixLift 601127
  have htrace : WordTrace (prefixWord ++ tailWord_601127) baseStart_601127 baseEnd_601127 := by
    simpa [prefixWord, tailWord_601127, baseEnd_601127] using wordTrace_append hprefix tailTrace_601127
  have hstable : (prefixWord ++ tailWord_601127).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601127).length < 2 ^ (prefixWord ++ tailWord_601127).sum := by decide
  have hdescent : baseEnd_601127 < baseStart_601127 := by decide
  rcases family_descends (prefixWord ++ tailWord_601127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601131 : List Nat := [1, 1, 1, 1, 2, 1, 7, 3, 3]
def baseStart_601131 : Nat := 118140960795 + 601131 * 2 ^ 59
def prefixEnd_601131 : Nat := 4983230072969 + 3 ^ 40 * 601131 * 2
def baseEnd_601131 : Nat := 274372568282660271909293

theorem tailTrace_601131 : CollatzResearch.WordTrace tailWord_601131 prefixEnd_601131 274372568282660271909293 := by
  unfold tailWord_601131
  simp only [CollatzResearch.WordTrace]
  refine ⟨21925048785212526846331247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14616699190141684564220831 21925048785212526846331247)
  ·
    refine ⟨32887573177818790269496871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21925048785212526846331247 32887573177818790269496871)
    ·
      refine ⟨49331359766728185404245307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32887573177818790269496871 49331359766728185404245307)
      ·
        refine ⟨73997039650092278106367961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49331359766728185404245307 73997039650092278106367961)
        ·
          refine ⟨55497779737569208579775971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73997039650092278106367961 55497779737569208579775971)
          ·
            refine ⟨83246669606353812869663957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55497779737569208579775971 83246669606353812869663957)
            ·
              refine ⟨1951093818898917489132749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 83246669606353812869663957 1951093818898917489132749)
              ·
                refine ⟨731660182087094058424781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1951093818898917489132749 731660182087094058424781)
                ·
                  refine ⟨274372568282660271909293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 731660182087094058424781 274372568282660271909293)
                  ·
                    rfl

theorem cell20_601131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 3, 3].length) (baseStart_601131 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_601131 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_601131 prefixEnd_601131 := by exact prefixLift 601131
  have htrace : WordTrace (prefixWord ++ tailWord_601131) baseStart_601131 baseEnd_601131 := by
    simpa [prefixWord, tailWord_601131, baseEnd_601131] using wordTrace_append hprefix tailTrace_601131
  have hstable : (prefixWord ++ tailWord_601131).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601131).length < 2 ^ (prefixWord ++ tailWord_601131).sum := by decide
  have hdescent : baseEnd_601131 < baseStart_601131 := by decide
  rcases family_descends (prefixWord ++ tailWord_601131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601138 : List Nat := [3, 2, 1, 1, 2, 2, 2, 1, 6]
def baseStart_601138 : Nat := 118140960795 + 601138 * 2 ^ 59
def prefixEnd_601138 : Nat := 4983230072969 + 3 ^ 40 * 601138 * 2
def baseEnd_601138 : Nat := 274375763273399358675931

theorem tailTrace_601138 : CollatzResearch.WordTrace tailWord_601138 prefixEnd_601138 274375763273399358675931 := by
  unfold tailWord_601138
  simp only [CollatzResearch.WordTrace]
  refine ⟨5481326024046791760459017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14616869397458111361224045 5481326024046791760459017)
  ·
    refine ⟨4110994518035093820344263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5481326024046791760459017 4110994518035093820344263)
    ·
      refine ⟨6166491777052640730516395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4110994518035093820344263 6166491777052640730516395)
      ·
        refine ⟨9249737665578961095774593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6166491777052640730516395 9249737665578961095774593)
        ·
          refine ⟨6937303249184220821830945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9249737665578961095774593 6937303249184220821830945)
          ·
            refine ⟨5202977436888165616373209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6937303249184220821830945 5202977436888165616373209)
            ·
              refine ⟨3902233077666124212279907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5202977436888165616373209 3902233077666124212279907)
              ·
                refine ⟨5853349616499186318419861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3902233077666124212279907 5853349616499186318419861)
                ·
                  refine ⟨274375763273399358675931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5853349616499186318419861 274375763273399358675931)
                  ·
                    rfl

theorem cell20_601138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_601138 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_601138 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_601138 prefixEnd_601138 := by exact prefixLift 601138
  have htrace : WordTrace (prefixWord ++ tailWord_601138) baseStart_601138 baseEnd_601138 := by
    simpa [prefixWord, tailWord_601138, baseEnd_601138] using wordTrace_append hprefix tailTrace_601138
  have hstable : (prefixWord ++ tailWord_601138).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601138).length < 2 ^ (prefixWord ++ tailWord_601138).sum := by decide
  have hdescent : baseEnd_601138 < baseStart_601138 := by decide
  rcases family_descends (prefixWord ++ tailWord_601138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601155 : List Nat := [1, 1, 1, 3, 1, 2, 4, 5, 2]
def baseStart_601155 : Nat := 118140960795 + 601155 * 2 ^ 59
def prefixEnd_601155 : Nat := 4983230072969 + 3 ^ 40 * 601155 * 2
def baseEnd_601155 : Nat := 274383522536622855109195

theorem tailTrace_601155 : CollatzResearch.WordTrace tailWord_601155 prefixEnd_601155 274383522536622855109195 := by
  unfold tailWord_601155
  simp only [CollatzResearch.WordTrace]
  refine ⟨21925924137125578945204919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14617282758083719296803279 21925924137125578945204919)
  ·
    refine ⟨32888886205688368417807379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21925924137125578945204919 32888886205688368417807379)
    ·
      refine ⟨49333329308532552626711069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32888886205688368417807379 49333329308532552626711069)
      ·
        refine ⟨18499998490699707235016651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49333329308532552626711069 18499998490699707235016651)
        ·
          refine ⟨27749997736049560852524977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18499998490699707235016651 27749997736049560852524977)
          ·
            refine ⟨20812498302037170639393733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27749997736049560852524977 20812498302037170639393733)
            ·
              refine ⟨3902343431631969494886325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20812498302037170639393733 3902343431631969494886325)
              ·
                refine ⟨365844696715497140145593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3902343431631969494886325 365844696715497140145593)
                ·
                  refine ⟨274383522536622855109195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 365844696715497140145593 274383522536622855109195)
                  ·
                    rfl

theorem cell20_601155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 5, 2].length) (baseStart_601155 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_601155 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_601155 prefixEnd_601155 := by exact prefixLift 601155
  have htrace : WordTrace (prefixWord ++ tailWord_601155) baseStart_601155 baseEnd_601155 := by
    simpa [prefixWord, tailWord_601155, baseEnd_601155] using wordTrace_append hprefix tailTrace_601155
  have hstable : (prefixWord ++ tailWord_601155).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601155).length < 2 ^ (prefixWord ++ tailWord_601155).sum := by decide
  have hdescent : baseEnd_601155 < baseStart_601155 := by decide
  rcases family_descends (prefixWord ++ tailWord_601155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601165 : List Nat := [1, 6, 1, 1, 1, 3, 2, 2, 3]
def baseStart_601165 : Nat := 118140960795 + 601165 * 2 ^ 59
def prefixEnd_601165 : Nat := 4983230072969 + 3 ^ 40 * 601165 * 2
def baseEnd_601165 : Nat := 274388086809107264775821

theorem tailTrace_601165 : CollatzResearch.WordTrace tailWord_601165 prefixEnd_601165 274388086809107264775821 := by
  unfold tailWord_601165
  simp only [CollatzResearch.WordTrace]
  refine ⟨21926288867089350653068949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14617525911392900435379299 21926288867089350653068949)
  ·
    refine ⟨1027794790644813311862607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 21926288867089350653068949 1027794790644813311862607)
    ·
      refine ⟨1541692185967219967793911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1027794790644813311862607 1541692185967219967793911)
      ·
        refine ⟨2312538278950829951690867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1541692185967219967793911 2312538278950829951690867)
        ·
          refine ⟨3468807418426244927536301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2312538278950829951690867 3468807418426244927536301)
          ·
            refine ⟨1300802781909841847826113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3468807418426244927536301 1300802781909841847826113)
            ·
              refine ⟨975602086432381385869585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1300802781909841847826113 975602086432381385869585)
              ·
                refine ⟨731701564824286039402189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 975602086432381385869585 731701564824286039402189)
                ·
                  refine ⟨274388086809107264775821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 731701564824286039402189 274388086809107264775821)
                  ·
                    rfl

theorem cell20_601165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_601165 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_601165 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_601165 prefixEnd_601165 := by exact prefixLift 601165
  have htrace : WordTrace (prefixWord ++ tailWord_601165) baseStart_601165 baseEnd_601165 := by
    simpa [prefixWord, tailWord_601165, baseEnd_601165] using wordTrace_append hprefix tailTrace_601165
  have hstable : (prefixWord ++ tailWord_601165).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601165).length < 2 ^ (prefixWord ++ tailWord_601165).sum := by decide
  have hdescent : baseEnd_601165 < baseStart_601165 := by decide
  rcases family_descends (prefixWord ++ tailWord_601165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601169 : List Nat := [1, 2, 2, 1, 3, 1, 3, 4, 3]
def baseStart_601169 : Nat := 118140960795 + 601169 * 2 ^ 59
def prefixEnd_601169 : Nat := 4983230072969 + 3 ^ 40 * 601169 * 2
def baseEnd_601169 : Nat := 274389912518101028642471

theorem tailTrace_601169 : CollatzResearch.WordTrace tailWord_601169 prefixEnd_601169 274389912518101028642471 := by
  unfold tailWord_601169
  simp only [CollatzResearch.WordTrace]
  refine ⟨21926434759074859336214561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14617623172716572890809707 21926434759074859336214561)
  ·
    refine ⟨16444826069306144502160921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21926434759074859336214561 16444826069306144502160921)
    ·
      refine ⟨12333619551979608376620691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16444826069306144502160921 12333619551979608376620691)
      ·
        refine ⟨18500429327969412564931037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12333619551979608376620691 18500429327969412564931037)
        ·
          refine ⟨6937660997988529711849139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18500429327969412564931037 6937660997988529711849139)
          ·
            refine ⟨10406491496982794567773709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6937660997988529711849139 10406491496982794567773709)
            ·
              refine ⟨3902434311368547962915141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10406491496982794567773709 3902434311368547962915141)
              ·
                refine ⟨731706433381602743046589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3902434311368547962915141 731706433381602743046589)
                ·
                  refine ⟨274389912518101028642471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 731706433381602743046589 274389912518101028642471)
                  ·
                    rfl

theorem cell20_601169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 4, 3].length) (baseStart_601169 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_601169 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_601169 prefixEnd_601169 := by exact prefixLift 601169
  have htrace : WordTrace (prefixWord ++ tailWord_601169) baseStart_601169 baseEnd_601169 := by
    simpa [prefixWord, tailWord_601169, baseEnd_601169] using wordTrace_append hprefix tailTrace_601169
  have hstable : (prefixWord ++ tailWord_601169).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601169).length < 2 ^ (prefixWord ++ tailWord_601169).sum := by decide
  have hdescent : baseEnd_601169 < baseStart_601169 := by decide
  rcases family_descends (prefixWord ++ tailWord_601169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601176 : List Nat := [2, 1, 2, 2, 1, 3, 2, 3, 4]
def baseStart_601176 : Nat := 118140960795 + 601176 * 2 ^ 59
def prefixEnd_601176 : Nat := 4983230072969 + 3 ^ 40 * 601176 * 2
def baseEnd_601176 : Nat := 274393107508840115409109

theorem tailTrace_601176 : CollatzResearch.WordTrace tailWord_601176 prefixEnd_601176 274393107508840115409109 := by
  unfold tailWord_601176
  simp only [CollatzResearch.WordTrace]
  refine ⟨10963345035024749765859691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14617793380032999687812921 10963345035024749765859691)
  ·
    refine ⟨16445017552537124648789537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10963345035024749765859691 16445017552537124648789537)
    ·
      refine ⟨12333763164402843486592153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16445017552537124648789537 12333763164402843486592153)
      ·
        refine ⟨9250322373302132614944115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12333763164402843486592153 9250322373302132614944115)
        ·
          refine ⟨13875483559953198922416173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9250322373302132614944115 13875483559953198922416173)
          ·
            refine ⟨5203306334982449595906065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13875483559953198922416173 5203306334982449595906065)
            ·
              refine ⟨3902479751236837196929549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5203306334982449595906065 3902479751236837196929549)
              ·
                refine ⟨1463429906713813948848581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3902479751236837196929549 1463429906713813948848581)
                ·
                  refine ⟨274393107508840115409109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1463429906713813948848581 274393107508840115409109)
                  ·
                    rfl

theorem cell20_601176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 3, 4].length) (baseStart_601176 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_601176 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_601176 prefixEnd_601176 := by exact prefixLift 601176
  have htrace : WordTrace (prefixWord ++ tailWord_601176) baseStart_601176 baseEnd_601176 := by
    simpa [prefixWord, tailWord_601176, baseEnd_601176] using wordTrace_append hprefix tailTrace_601176
  have hstable : (prefixWord ++ tailWord_601176).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601176).length < 2 ^ (prefixWord ++ tailWord_601176).sum := by decide
  have hdescent : baseEnd_601176 < baseStart_601176 := by decide
  rcases family_descends (prefixWord ++ tailWord_601176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601182 : List Nat := [4, 4, 1, 1, 1, 1, 2, 3, 3]
def baseStart_601182 : Nat := 118140960795 + 601182 * 2 ^ 59
def prefixEnd_601182 : Nat := 4983230072969 + 3 ^ 40 * 601182 * 2
def baseEnd_601182 : Nat := 274395846072330761209085

theorem tailTrace_601182 : CollatzResearch.WordTrace tailWord_601182 prefixEnd_601182 274395846072330761209085 := by
  unfold tailWord_601182
  simp only [CollatzResearch.WordTrace]
  refine ⟨2740863613503470319554725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14617939272018508370958533 2740863613503470319554725)
  ·
    refine ⟨513911927531900684916511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2740863613503470319554725 513911927531900684916511)
    ·
      refine ⟨770867891297851027374767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 513911927531900684916511 770867891297851027374767)
      ·
        refine ⟨1156301836946776541062151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 770867891297851027374767 1156301836946776541062151)
        ·
          refine ⟨1734452755420164811593227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1156301836946776541062151 1734452755420164811593227)
          ·
            refine ⟨2601679133130247217389841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1734452755420164811593227 2601679133130247217389841)
            ·
              refine ⟨1951259349847685413042381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2601679133130247217389841 1951259349847685413042381)
              ·
                refine ⟨731722256192882029890893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1951259349847685413042381 731722256192882029890893)
                ·
                  refine ⟨274395846072330761209085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 731722256192882029890893 274395846072330761209085)
                  ·
                    rfl

theorem cell20_601182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_601182 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_601182 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_601182 prefixEnd_601182 := by exact prefixLift 601182
  have htrace : WordTrace (prefixWord ++ tailWord_601182) baseStart_601182 baseEnd_601182 := by
    simpa [prefixWord, tailWord_601182, baseEnd_601182] using wordTrace_append hprefix tailTrace_601182
  have hstable : (prefixWord ++ tailWord_601182).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601182).length < 2 ^ (prefixWord ++ tailWord_601182).sum := by decide
  have hdescent : baseEnd_601182 < baseStart_601182 := by decide
  rcases family_descends (prefixWord ++ tailWord_601182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601200 : List Nat := [2, 1, 1, 1, 5, 1, 5, 4]
def baseStart_601200 : Nat := 118140960795 + 601200 * 2 ^ 59
def prefixEnd_601200 : Nat := 4983230072969 + 3 ^ 40 * 601200 * 2
def baseEnd_601200 : Nat := 91468020587600899536337

theorem tailTrace_601200 : CollatzResearch.WordTrace tailWord_601200 prefixEnd_601200 91468020587600899536337 := by
  unfold tailWord_601200
  simp only [CollatzResearch.WordTrace]
  refine ⟨10963782710981275815296527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14618376947975034420395369 10963782710981275815296527)
  ·
    refine ⟨16445674066471913722944791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10963782710981275815296527 16445674066471913722944791)
    ·
      refine ⟨24668511099707870584417187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16445674066471913722944791 24668511099707870584417187)
      ·
        refine ⟨37002766649561805876625781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24668511099707870584417187 37002766649561805876625781)
        ·
          refine ⟨3469009373396419300933667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37002766649561805876625781 3469009373396419300933667)
          ·
            refine ⟨5203514060094628951400501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3469009373396419300933667 5203514060094628951400501)
            ·
              refine ⟨487829443133871464193797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5203514060094628951400501 487829443133871464193797)
              ·
                refine ⟨91468020587600899536337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 487829443133871464193797 91468020587600899536337)
                ·
                  rfl

theorem cell20_601200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 5, 4].length) (baseStart_601200 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_601200 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_601200 prefixEnd_601200 := by exact prefixLift 601200
  have htrace : WordTrace (prefixWord ++ tailWord_601200) baseStart_601200 baseEnd_601200 := by
    simpa [prefixWord, tailWord_601200, baseEnd_601200] using wordTrace_append hprefix tailTrace_601200
  have hstable : (prefixWord ++ tailWord_601200).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601200).length < 2 ^ (prefixWord ++ tailWord_601200).sum := by decide
  have hdescent : baseEnd_601200 < baseStart_601200 := by decide
  rcases family_descends (prefixWord ++ tailWord_601200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601224 : List Nat := [2, 1, 3, 4, 2, 1, 1, 1, 5]
def baseStart_601224 : Nat := 118140960795 + 601224 * 2 ^ 59
def prefixEnd_601224 : Nat := 4983230072969 + 3 ^ 40 * 601224 * 2
def baseEnd_601224 : Nat := 274415016016765281808913

theorem tailTrace_601224 : CollatzResearch.WordTrace tailWord_601224 prefixEnd_601224 274415016016765281808913 := by
  unfold tailWord_601224
  simp only [CollatzResearch.WordTrace]
  refine ⟨10964220386937801864733363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14618960515917069152977817 10964220386937801864733363)
  ·
    refine ⟨16446330580406702797100045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10964220386937801864733363 16446330580406702797100045)
    ·
      refine ⟨6167373967652513548912517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16446330580406702797100045 6167373967652513548912517)
      ·
        refine ⟨1156382618934846290421097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6167373967652513548912517 1156382618934846290421097)
        ·
          refine ⟨867286964201134717815823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1156382618934846290421097 867286964201134717815823)
          ·
            refine ⟨1300930446301702076723735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 867286964201134717815823 1300930446301702076723735)
            ·
              refine ⟨1951395669452553115085603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1300930446301702076723735 1951395669452553115085603)
              ·
                refine ⟨2927093504178829672628405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1951395669452553115085603 2927093504178829672628405)
                ·
                  refine ⟨274415016016765281808913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2927093504178829672628405 274415016016765281808913)
                  ·
                    rfl

theorem cell20_601224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 5].length) (baseStart_601224 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_601224 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_601224 prefixEnd_601224 := by exact prefixLift 601224
  have htrace : WordTrace (prefixWord ++ tailWord_601224) baseStart_601224 baseEnd_601224 := by
    simpa [prefixWord, tailWord_601224, baseEnd_601224] using wordTrace_append hprefix tailTrace_601224
  have hstable : (prefixWord ++ tailWord_601224).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601224).length < 2 ^ (prefixWord ++ tailWord_601224).sum := by decide
  have hdescent : baseEnd_601224 < baseStart_601224 := by decide
  rcases family_descends (prefixWord ++ tailWord_601224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601255 : List Nat := [1, 1, 6, 2, 1, 1, 4, 4]
def baseStart_601255 : Nat := 118140960795 + 601255 * 2 ^ 59
def prefixEnd_601255 : Nat := 4983230072969 + 3 ^ 40 * 601255 * 2
def baseEnd_601255 : Nat := 91476388420488983925151

theorem tailTrace_601255 : CollatzResearch.WordTrace tailWord_601255 prefixEnd_601255 91476388420488983925151 := by
  unfold tailWord_601255
  simp only [CollatzResearch.WordTrace]
  refine ⟨21929571436763296023845219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14619714291175530682563479 21929571436763296023845219)
  ·
    refine ⟨32894357155144944035767829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21929571436763296023845219 32894357155144944035767829)
    ·
      refine ⟨1541922991647419251676617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 32894357155144944035767829 1541922991647419251676617)
      ·
        refine ⟨1156442243735564438757463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1541922991647419251676617 1156442243735564438757463)
        ·
          refine ⟨1734663365603346658136195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1156442243735564438757463 1734663365603346658136195)
          ·
            refine ⟨2601995048405019987204293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1734663365603346658136195 2601995048405019987204293)
            ·
              refine ⟨487874071575941247600805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2601995048405019987204293 487874071575941247600805)
              ·
                refine ⟨91476388420488983925151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 487874071575941247600805 91476388420488983925151)
                ·
                  rfl

theorem cell20_601255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 4, 4].length) (baseStart_601255 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_601255 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_601255 prefixEnd_601255 := by exact prefixLift 601255
  have htrace : WordTrace (prefixWord ++ tailWord_601255) baseStart_601255 baseEnd_601255 := by
    simpa [prefixWord, tailWord_601255, baseEnd_601255] using wordTrace_append hprefix tailTrace_601255
  have hstable : (prefixWord ++ tailWord_601255).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601255).length < 2 ^ (prefixWord ++ tailWord_601255).sum := by decide
  have hdescent : baseEnd_601255 < baseStart_601255 := by decide
  rcases family_descends (prefixWord ++ tailWord_601255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601265 : List Nat := [1, 2, 2, 5, 1, 3, 1, 3, 2]
def baseStart_601265 : Nat := 118140960795 + 601265 * 2 ^ 59
def prefixEnd_601265 : Nat := 4983230072969 + 3 ^ 40 * 601265 * 2
def baseEnd_601265 : Nat := 274433729533951361442079

theorem tailTrace_601265 : CollatzResearch.WordTrace tailWord_601265 prefixEnd_601265 274433729533951361442079 := by
  unfold tailWord_601265
  simp only [CollatzResearch.WordTrace]
  refine ⟨21929936166727067731709249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14619957444484711821139499 21929936166727067731709249)
  ·
    refine ⟨16447452125045300798781937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21929936166727067731709249 16447452125045300798781937)
    ·
      refine ⟨12335589093783975599086453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16447452125045300798781937 12335589093783975599086453)
      ·
        refine ⟨1156461477542247712414355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12335589093783975599086453 1156461477542247712414355)
        ·
          refine ⟨1734692216313371568621533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1156461477542247712414355 1734692216313371568621533)
          ·
            refine ⟨650509581117514338233075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1734692216313371568621533 650509581117514338233075)
            ·
              refine ⟨975764371676271507349613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 650509581117514338233075 975764371676271507349613)
              ·
                refine ⟨365911639378601815256105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 975764371676271507349613 365911639378601815256105)
                ·
                  refine ⟨274433729533951361442079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 365911639378601815256105 274433729533951361442079)
                  ·
                    rfl

theorem cell20_601265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 3, 2].length) (baseStart_601265 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_601265 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_601265 prefixEnd_601265 := by exact prefixLift 601265
  have htrace : WordTrace (prefixWord ++ tailWord_601265) baseStart_601265 baseEnd_601265 := by
    simpa [prefixWord, tailWord_601265, baseEnd_601265] using wordTrace_append hprefix tailTrace_601265
  have hstable : (prefixWord ++ tailWord_601265).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601265).length < 2 ^ (prefixWord ++ tailWord_601265).sum := by decide
  have hdescent : baseEnd_601265 < baseStart_601265 := by decide
  rcases family_descends (prefixWord ++ tailWord_601265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601276 : List Nat := [2, 2, 2, 3, 2, 3, 6]
def baseStart_601276 : Nat := 118140960795 + 601276 * 2 ^ 59
def prefixEnd_601276 : Nat := 4983230072969 + 3 ^ 40 * 601276 * 2
def baseEnd_601276 : Nat := 30493194470409356897263

theorem tailTrace_601276 : CollatzResearch.WordTrace tailWord_601276 prefixEnd_601276 30493194470409356897263 := by
  unfold tailWord_601276
  simp only [CollatzResearch.WordTrace]
  refine ⟨10965168684843608305179841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14620224913124811073573121 10965168684843608305179841)
  ·
    refine ⟨8223876513632706228884881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10965168684843608305179841 8223876513632706228884881)
    ·
      refine ⟨6167907385224529671663661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8223876513632706228884881 6167907385224529671663661)
      ·
        refine ⟨2312965269459198626873873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6167907385224529671663661 2312965269459198626873873)
        ·
          refine ⟨1734723952094398970155405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2312965269459198626873873 1734723952094398970155405)
          ·
            refine ⟨650521482035399613808277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1734723952094398970155405 650521482035399613808277)
            ·
              refine ⟨30493194470409356897263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 650521482035399613808277 30493194470409356897263)
              ·
                rfl

theorem cell20_601276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 6].length) (baseStart_601276 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_601276 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_601276 prefixEnd_601276 := by exact prefixLift 601276
  have htrace : WordTrace (prefixWord ++ tailWord_601276) baseStart_601276 baseEnd_601276 := by
    simpa [prefixWord, tailWord_601276, baseEnd_601276] using wordTrace_append hprefix tailTrace_601276
  have hstable : (prefixWord ++ tailWord_601276).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601276).length < 2 ^ (prefixWord ++ tailWord_601276).sum := by decide
  have hdescent : baseEnd_601276 < baseStart_601276 := by decide
  rcases family_descends (prefixWord ++ tailWord_601276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601282 : List Nat := [3, 5, 1, 1, 2, 2, 1, 1, 4]
def baseStart_601282 : Nat := 118140960795 + 601282 * 2 ^ 59
def prefixEnd_601282 : Nat := 4983230072969 + 3 ^ 40 * 601282 * 2
def baseEnd_601282 : Nat := 274441488797174857875343

theorem tailTrace_601282 : CollatzResearch.WordTrace tailWord_601282 prefixEnd_601282 274441488797174857875343 := by
  unfold tailWord_601282
  simp only [CollatzResearch.WordTrace]
  refine ⟨5482639051916369908769525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14620370805110319756718733 5482639051916369908769525)
  ·
    refine ⟨513997411117159678947143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5482639051916369908769525 513997411117159678947143)
    ·
      refine ⟨770996116675739518420715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 513997411117159678947143 770996116675739518420715)
      ·
        refine ⟨1156494175013609277631073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 770996116675739518420715 1156494175013609277631073)
        ·
          refine ⟨867370631260206958223305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1156494175013609277631073 867370631260206958223305)
          ·
            refine ⟨650527973445155218667479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 867370631260206958223305 650527973445155218667479)
            ·
              refine ⟨975791960167732828001219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 650527973445155218667479 975791960167732828001219)
              ·
                refine ⟨1463687940251599242001829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 975791960167732828001219 1463687940251599242001829)
                ·
                  refine ⟨274441488797174857875343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1463687940251599242001829 274441488797174857875343)
                  ·
                    rfl

theorem cell20_601282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_601282 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_601282 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_601282 prefixEnd_601282 := by exact prefixLift 601282
  have htrace : WordTrace (prefixWord ++ tailWord_601282) baseStart_601282 baseEnd_601282 := by
    simpa [prefixWord, tailWord_601282, baseEnd_601282] using wordTrace_append hprefix tailTrace_601282
  have hstable : (prefixWord ++ tailWord_601282).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601282).length < 2 ^ (prefixWord ++ tailWord_601282).sum := by decide
  have hdescent : baseEnd_601282 < baseStart_601282 := by decide
  rcases family_descends (prefixWord ++ tailWord_601282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601397 : List Nat := [1, 3, 3, 1, 2, 3, 1, 1, 5]
def baseStart_601397 : Nat := 118140960795 + 601397 * 2 ^ 59
def prefixEnd_601397 : Nat := 4983230072969 + 3 ^ 40 * 601397 * 2
def baseEnd_601397 : Nat := 274493977930745569041539

theorem tailTrace_601397 : CollatzResearch.WordTrace tailWord_601397 prefixEnd_601397 274493977930745569041539 := by
  unfold tailWord_601397
  simp only [CollatzResearch.WordTrace]
  refine ⟨21934750602248854275514445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14623167068165902850342963 21934750602248854275514445)
  ·
    refine ⟨8225531475843320353317917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21934750602248854275514445 8225531475843320353317917)
    ·
      refine ⟨3084574303441245132494219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8225531475843320353317917 3084574303441245132494219)
      ·
        refine ⟨4626861455161867698741329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3084574303441245132494219 4626861455161867698741329)
        ·
          refine ⟨3470146091371400774055997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4626861455161867698741329 3470146091371400774055997)
          ·
            refine ⟨1301304784264275290270999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3470146091371400774055997 1301304784264275290270999)
            ·
              refine ⟨1951957176396412935406499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1301304784264275290270999 1951957176396412935406499)
              ·
                refine ⟨2927935764594619403109749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1951957176396412935406499 2927935764594619403109749)
                ·
                  refine ⟨274493977930745569041539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2927935764594619403109749 274493977930745569041539)
                  ·
                    rfl

theorem cell20_601397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 5].length) (baseStart_601397 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_601397 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_601397 prefixEnd_601397 := by exact prefixLift 601397
  have htrace : WordTrace (prefixWord ++ tailWord_601397) baseStart_601397 baseEnd_601397 := by
    simpa [prefixWord, tailWord_601397, baseEnd_601397] using wordTrace_append hprefix tailTrace_601397
  have hstable : (prefixWord ++ tailWord_601397).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601397).length < 2 ^ (prefixWord ++ tailWord_601397).sum := by decide
  have hdescent : baseEnd_601397 < baseStart_601397 := by decide
  rcases family_descends (prefixWord ++ tailWord_601397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
