import V185TrunkScan23Chunk1198

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7103409 : List Nat := [1, 2, 2, 4, 3, 2, 1, 1, 1, 4, 2]
def baseStart_7103409 : Nat := 118140960795 + 7103409 * 2 ^ 59
def prefixEnd_7103409 : Nat := 4983230072969 + 3 ^ 40 * 7103409 * 2
def baseEnd_7103409 : Nat := 3647463102473503613319523

theorem tailTrace_7103409 : CollatzResearch.WordTrace tailWord_7103409 prefixEnd_7103409 3647463102473503613319523 := by
  unfold tailWord_7103409
  simp only [CollatzResearch.WordTrace]
  refine ⟨259082610722569833517257281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172721740481713222344838187 259082610722569833517257281)
  ·
    refine ⟨194311958041927375137942961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259082610722569833517257281 194311958041927375137942961)
    ·
      refine ⟨145733968531445531353457221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194311958041927375137942961 145733968531445531353457221)
      ·
        refine ⟨27325119099646037128773229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145733968531445531353457221 27325119099646037128773229)
        ·
          refine ⟨10246919662367263923289961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27325119099646037128773229 10246919662367263923289961)
          ·
            refine ⟨7685189746775447942467471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10246919662367263923289961 7685189746775447942467471)
            ·
              refine ⟨11527784620163171913701207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7685189746775447942467471 11527784620163171913701207)
              ·
                refine ⟨17291676930244757870551811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11527784620163171913701207 17291676930244757870551811)
                ·
                  refine ⟨25937515395367136805827717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17291676930244757870551811 25937515395367136805827717)
                  ·
                    refine ⟨4863284136631338151092697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25937515395367136805827717 4863284136631338151092697)
                    ·
                      refine ⟨3647463102473503613319523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4863284136631338151092697 3647463102473503613319523)
                      ·
                        rfl

theorem cell23_7103409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 1, 1, 4, 2].length) (baseStart_7103409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7103409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7103409 prefixEnd_7103409 := by exact prefixLift 7103409
  have htrace : WordTrace (prefixWord ++ tailWord_7103409) baseStart_7103409 baseEnd_7103409 := by
    simpa [prefixWord, tailWord_7103409, baseEnd_7103409] using wordTrace_append hprefix tailTrace_7103409
  have hstable : (prefixWord ++ tailWord_7103409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7103409).length < 2 ^ (prefixWord ++ tailWord_7103409).sum := by decide
  have hdescent : baseEnd_7103409 < baseStart_7103409 := by decide
  rcases family_descends (prefixWord ++ tailWord_7103409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7103455 : List Nat := [1, 1, 2, 3, 5, 1, 1, 1, 1, 2, 5]
def baseStart_7103455 : Nat := 118140960795 + 7103455 * 2 ^ 59
def prefixEnd_7103455 : Nat := 4983230072969 + 3 ^ 40 * 7103455 * 2
def baseEnd_7103455 : Nat := 3647486722583610433344311

theorem tailTrace_7103455 : CollatzResearch.WordTrace tailWord_7103455 prefixEnd_7103455 3647486722583610433344311 := by
  unfold tailWord_7103455
  simp only [CollatzResearch.WordTrace]
  refine ⟨259084288480403183373431819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172722858986935455582287879 259084288480403183373431819)
  ·
    refine ⟨388626432720604775060147729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259084288480403183373431819 388626432720604775060147729)
    ·
      refine ⟨291469824540453581295110797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 388626432720604775060147729 291469824540453581295110797)
      ·
        refine ⟨109301184202670092985666549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 291469824540453581295110797 109301184202670092985666549)
        ·
          refine ⟨10246986019000321217406239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 109301184202670092985666549 10246986019000321217406239)
          ·
            refine ⟨15370479028500481826109359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10246986019000321217406239 15370479028500481826109359)
            ·
              refine ⟨23055718542750722739164039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15370479028500481826109359 23055718542750722739164039)
              ·
                refine ⟨34583577814126084108746059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23055718542750722739164039 34583577814126084108746059)
                ·
                  refine ⟨51875366721189126163119089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34583577814126084108746059 51875366721189126163119089)
                  ·
                    refine ⟨38906525040891844622339317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51875366721189126163119089 38906525040891844622339317)
                    ·
                      refine ⟨3647486722583610433344311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38906525040891844622339317 3647486722583610433344311)
                      ·
                        rfl

theorem cell23_7103455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 2, 5].length) (baseStart_7103455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7103455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7103455 prefixEnd_7103455 := by exact prefixLift 7103455
  have htrace : WordTrace (prefixWord ++ tailWord_7103455) baseStart_7103455 baseEnd_7103455 := by
    simpa [prefixWord, tailWord_7103455, baseEnd_7103455] using wordTrace_append hprefix tailTrace_7103455
  have hstable : (prefixWord ++ tailWord_7103455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7103455).length < 2 ^ (prefixWord ++ tailWord_7103455).sum := by decide
  have hdescent : baseEnd_7103455 < baseStart_7103455 := by decide
  rcases family_descends (prefixWord ++ tailWord_7103455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7103502 : List Nat := [4, 1, 1, 2, 2, 2, 2, 2, 2, 2, 3]
def baseStart_7103502 : Nat := 118140960795 + 7103502 * 2 ^ 59
def prefixEnd_7103502 : Nat := 4983230072969 + 3 ^ 40 * 7103502 * 2
def baseEnd_7103502 : Nat := 3647510856174371749456595

theorem tailTrace_7103502 : CollatzResearch.WordTrace tailWord_7103502 prefixEnd_7103502 3647510856174371749456595 := by
  unfold tailWord_7103502
  simp only [CollatzResearch.WordTrace]
  refine ⟨32385750338904113800049095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172724001807488606933595173 32385750338904113800049095)
  ·
    refine ⟨48578625508356170700073643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32385750338904113800049095 48578625508356170700073643)
    ·
      refine ⟨72867938262534256050110465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48578625508356170700073643 72867938262534256050110465)
      ·
        refine ⟨54650953696900692037582849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72867938262534256050110465 54650953696900692037582849)
        ·
          refine ⟨40988215272675519028187137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54650953696900692037582849 40988215272675519028187137)
          ·
            refine ⟨30741161454506639271140353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40988215272675519028187137 30741161454506639271140353)
            ·
              refine ⟨23055871090879979453355265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30741161454506639271140353 23055871090879979453355265)
              ·
                refine ⟨17291903318159984590016449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23055871090879979453355265 17291903318159984590016449)
                ·
                  refine ⟨12968927488619988442512337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17291903318159984590016449 12968927488619988442512337)
                  ·
                    refine ⟨9726695616464991331884253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12968927488619988442512337 9726695616464991331884253)
                    ·
                      refine ⟨3647510856174371749456595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9726695616464991331884253 3647510856174371749456595)
                      ·
                        rfl

theorem cell23_7103502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 2, 2, 2, 3].length) (baseStart_7103502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7103502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7103502 prefixEnd_7103502 := by exact prefixLift 7103502
  have htrace : WordTrace (prefixWord ++ tailWord_7103502) baseStart_7103502 baseEnd_7103502 := by
    simpa [prefixWord, tailWord_7103502, baseEnd_7103502] using wordTrace_append hprefix tailTrace_7103502
  have hstable : (prefixWord ++ tailWord_7103502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7103502).length < 2 ^ (prefixWord ++ tailWord_7103502).sum := by decide
  have hdescent : baseEnd_7103502 < baseStart_7103502 := by decide
  rcases family_descends (prefixWord ++ tailWord_7103502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7103509 : List Nat := [1, 3, 2, 1, 4, 2, 1, 4, 1, 4]
def baseStart_7103509 : Nat := 118140960795 + 7103509 * 2 ^ 59
def prefixEnd_7103509 : Nat := 4983230072969 + 3 ^ 40 * 7103509 * 2
def baseEnd_7103509 : Nat := 1215838150179651074023021

theorem tailTrace_7103509 : CollatzResearch.WordTrace tailWord_7103509 prefixEnd_7103509 1215838150179651074023021 := by
  unfold tailWord_7103509
  simp only [CollatzResearch.WordTrace]
  refine ⟨259086258022207550595897581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172724172014805033730598387 259086258022207550595897581)
  ·
    refine ⟨97157346758327831473461593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259086258022207550595897581 97157346758327831473461593)
    ·
      refine ⟨72868010068745873605096195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97157346758327831473461593 72868010068745873605096195)
      ·
        refine ⟨109302015103118810407644293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72868010068745873605096195 109302015103118810407644293)
        ·
          refine ⟨20494127831834776951433305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109302015103118810407644293 20494127831834776951433305)
          ·
            refine ⟨15370595873876082713574979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20494127831834776951433305 15370595873876082713574979)
            ·
              refine ⟨23055893810814124070362469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15370595873876082713574979 23055893810814124070362469)
              ·
                refine ⟨4322980089527648263192963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23055893810814124070362469 4322980089527648263192963)
                ·
                  refine ⟨6484470134291472394789445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4322980089527648263192963 6484470134291472394789445)
                  ·
                    refine ⟨1215838150179651074023021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6484470134291472394789445 1215838150179651074023021)
                    ·
                      rfl

theorem cell23_7103509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 4, 1, 4].length) (baseStart_7103509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7103509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7103509 prefixEnd_7103509 := by exact prefixLift 7103509
  have htrace : WordTrace (prefixWord ++ tailWord_7103509) baseStart_7103509 baseEnd_7103509 := by
    simpa [prefixWord, tailWord_7103509, baseEnd_7103509] using wordTrace_append hprefix tailTrace_7103509
  have hstable : (prefixWord ++ tailWord_7103509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7103509).length < 2 ^ (prefixWord ++ tailWord_7103509).sum := by decide
  have hdescent : baseEnd_7103509 < baseStart_7103509 := by decide
  rcases family_descends (prefixWord ++ tailWord_7103509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7103532 : List Nat := [2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 3]
def baseStart_7103532 : Nat := 118140960795 + 7103532 * 2 ^ 59
def prefixEnd_7103532 : Nat := 4983230072969 + 3 ^ 40 * 7103532 * 2
def baseEnd_7103532 : Nat := 3647526260594006632081457

theorem tailTrace_7103532 : CollatzResearch.WordTrace tailWord_7103532 prefixEnd_7103532 3647526260594006632081457 := by
  unfold tailWord_7103532
  simp only [CollatzResearch.WordTrace]
  refine ⟨129543548450562112761992425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172724731267416150349323233 129543548450562112761992425)
  ·
    refine ⟨97157661337921584571494319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129543548450562112761992425 97157661337921584571494319)
    ·
      refine ⟨145736492006882376857241479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97157661337921584571494319 145736492006882376857241479)
      ·
        refine ⟨218604738010323565285862219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145736492006882376857241479 218604738010323565285862219)
        ·
          refine ⟨327907107015485347928793329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218604738010323565285862219 327907107015485347928793329)
          ·
            refine ⟨245930330261614010946594997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 327907107015485347928793329 245930330261614010946594997)
            ·
              refine ⟨23055968462026313526243281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 245930330261614010946594997 23055968462026313526243281)
              ·
                refine ⟨17291976346519735144682461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23055968462026313526243281 17291976346519735144682461)
                ·
                  refine ⟨6484491129944900679255923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17291976346519735144682461 6484491129944900679255923)
                  ·
                    refine ⟨9726736694917351018883885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6484491129944900679255923 9726736694917351018883885)
                    ·
                      refine ⟨3647526260594006632081457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9726736694917351018883885 3647526260594006632081457)
                      ·
                        rfl

theorem cell23_7103532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 3].length) (baseStart_7103532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7103532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7103532 prefixEnd_7103532 := by exact prefixLift 7103532
  have htrace : WordTrace (prefixWord ++ tailWord_7103532) baseStart_7103532 baseEnd_7103532 := by
    simpa [prefixWord, tailWord_7103532, baseEnd_7103532] using wordTrace_append hprefix tailTrace_7103532
  have hstable : (prefixWord ++ tailWord_7103532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7103532).length < 2 ^ (prefixWord ++ tailWord_7103532).sum := by decide
  have hdescent : baseEnd_7103532 < baseStart_7103532 := by decide
  rcases family_descends (prefixWord ++ tailWord_7103532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7103589 : List Nat := [1, 3, 1, 3, 2, 1, 1, 4, 3, 2, 2]
def baseStart_7103589 : Nat := 118140960795 + 7103589 * 2 ^ 59
def prefixEnd_7103589 : Nat := 4983230072969 + 3 ^ 40 * 7103589 * 2
def baseEnd_7103589 : Nat := 3647555528991312909068695

theorem tailTrace_7103589 : CollatzResearch.WordTrace tailWord_7103589 prefixEnd_7103589 3647555528991312909068695 := by
  unfold tailWord_7103589
  simp only [CollatzResearch.WordTrace]
  refine ⟨259089175861917724258809821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172726117241278482839206547 259089175861917724258809821)
  ·
    refine ⟨97158440948219146597053683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259089175861917724258809821 97158440948219146597053683)
    ·
      refine ⟨145737661422328719895580525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97158440948219146597053683 145737661422328719895580525)
      ·
        refine ⟨54651623033373269960842697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145737661422328719895580525 54651623033373269960842697)
        ·
          refine ⟨40988717275029952470632023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54651623033373269960842697 40988717275029952470632023)
          ·
            refine ⟨61483075912544928705948035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40988717275029952470632023 61483075912544928705948035)
            ·
              refine ⟨92224613868817393058922053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61483075912544928705948035 92224613868817393058922053)
              ·
                refine ⟨17292115100403261198547885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92224613868817393058922053 17292115100403261198547885)
                ·
                  refine ⟨6484543162651222949455457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17292115100403261198547885 6484543162651222949455457)
                  ·
                    refine ⟨4863407371988417212091593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6484543162651222949455457 4863407371988417212091593)
                    ·
                      refine ⟨3647555528991312909068695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4863407371988417212091593 3647555528991312909068695)
                      ·
                        rfl

theorem cell23_7103589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 4, 3, 2, 2].length) (baseStart_7103589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7103589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7103589 prefixEnd_7103589 := by exact prefixLift 7103589
  have htrace : WordTrace (prefixWord ++ tailWord_7103589) baseStart_7103589 baseEnd_7103589 := by
    simpa [prefixWord, tailWord_7103589, baseEnd_7103589] using wordTrace_append hprefix tailTrace_7103589
  have hstable : (prefixWord ++ tailWord_7103589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7103589).length < 2 ^ (prefixWord ++ tailWord_7103589).sum := by decide
  have hdescent : baseEnd_7103589 < baseStart_7103589 := by decide
  rcases family_descends (prefixWord ++ tailWord_7103589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7103649 : List Nat := [1, 2, 3, 3, 1, 1, 3, 1, 3, 3, 2]
def baseStart_7103649 : Nat := 118140960795 + 7103649 * 2 ^ 59
def prefixEnd_7103649 : Nat := 4983230072969 + 3 ^ 40 * 7103649 * 2
def baseEnd_7103649 : Nat := 3647586337830582674318419

theorem tailTrace_7103649 : CollatzResearch.WordTrace tailWord_7103649 prefixEnd_7103649 3647586337830582674318419 := by
  unfold tailWord_7103649
  simp only [CollatzResearch.WordTrace]
  refine ⟨259091364241700354505994001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172727576161133569670662667 259091364241700354505994001)
  ·
    refine ⟨194318523181275265879495501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259091364241700354505994001 194318523181275265879495501)
    ·
      refine ⟨72869446192978224704810813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194318523181275265879495501 72869446192978224704810813)
      ·
        refine ⟨27326042322366834264304055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72869446192978224704810813 27326042322366834264304055)
        ·
          refine ⟨40989063483550251396456083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27326042322366834264304055 40989063483550251396456083)
          ·
            refine ⟨61483595225325377094684125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40989063483550251396456083 61483595225325377094684125)
            ·
              refine ⟨23056348209497016410506547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61483595225325377094684125 23056348209497016410506547)
              ·
                refine ⟨34584522314245524615759821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23056348209497016410506547 34584522314245524615759821)
                ·
                  refine ⟨12969195867842071730909933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34584522314245524615759821 12969195867842071730909933)
                  ·
                    refine ⟨4863448450440776899091225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12969195867842071730909933 4863448450440776899091225)
                    ·
                      refine ⟨3647586337830582674318419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4863448450440776899091225 3647586337830582674318419)
                      ·
                        rfl

theorem cell23_7103649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 3, 3, 2].length) (baseStart_7103649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7103649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7103649 prefixEnd_7103649 := by exact prefixLift 7103649
  have htrace : WordTrace (prefixWord ++ tailWord_7103649) baseStart_7103649 baseEnd_7103649 := by
    simpa [prefixWord, tailWord_7103649, baseEnd_7103649] using wordTrace_append hprefix tailTrace_7103649
  have hstable : (prefixWord ++ tailWord_7103649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7103649).length < 2 ^ (prefixWord ++ tailWord_7103649).sum := by decide
  have hdescent : baseEnd_7103649 < baseStart_7103649 := by decide
  rcases family_descends (prefixWord ++ tailWord_7103649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7103679 : List Nat := [1, 1, 2, 2, 2, 2, 2, 3, 4, 2, 2]
def baseStart_7103679 : Nat := 118140960795 + 7103679 * 2 ^ 59
def prefixEnd_7103679 : Nat := 4983230072969 + 3 ^ 40 * 7103679 * 2
def baseEnd_7103679 : Nat := 3647601742250217556943281

theorem tailTrace_7103679 : CollatzResearch.WordTrace tailWord_7103679 prefixEnd_7103679 3647601742250217556943281 := by
  unfold tailWord_7103679
  simp only [CollatzResearch.WordTrace]
  refine ⟨259092458431591669629586091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172728305621061113086390727 259092458431591669629586091)
  ·
    refine ⟨388638687647387504444379137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259092458431591669629586091 388638687647387504444379137)
    ·
      refine ⟨291479015735540628333284353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 388638687647387504444379137 291479015735540628333284353)
      ·
        refine ⟨218609261801655471249963265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291479015735540628333284353 218609261801655471249963265)
        ·
          refine ⟨163956946351241603437472449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218609261801655471249963265 163956946351241603437472449)
          ·
            refine ⟨122967709763431202578104337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163956946351241603437472449 122967709763431202578104337)
            ·
              refine ⟨92225782322573401933578253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122967709763431202578104337 92225782322573401933578253)
              ·
                refine ⟨34584668370965025725091845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92225782322573401933578253 34584668370965025725091845)
                ·
                  refine ⟨6484625319555942323454721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34584668370965025725091845 6484625319555942323454721)
                  ·
                    refine ⟨4863468989666956742591041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6484625319555942323454721 4863468989666956742591041)
                    ·
                      refine ⟨3647601742250217556943281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4863468989666956742591041 3647601742250217556943281)
                      ·
                        rfl

theorem cell23_7103679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 4, 2, 2].length) (baseStart_7103679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7103679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7103679 prefixEnd_7103679 := by exact prefixLift 7103679
  have htrace : WordTrace (prefixWord ++ tailWord_7103679) baseStart_7103679 baseEnd_7103679 := by
    simpa [prefixWord, tailWord_7103679, baseEnd_7103679] using wordTrace_append hprefix tailTrace_7103679
  have hstable : (prefixWord ++ tailWord_7103679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7103679).length < 2 ^ (prefixWord ++ tailWord_7103679).sum := by decide
  have hdescent : baseEnd_7103679 < baseStart_7103679 := by decide
  rcases family_descends (prefixWord ++ tailWord_7103679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7103685 : List Nat := [1, 3, 1, 1, 1, 1, 3, 5, 7]
def baseStart_7103685 : Nat := 118140960795 + 7103685 * 2 ^ 59
def prefixEnd_7103685 : Nat := 4983230072969 + 3 ^ 40 * 7103685 * 2
def baseEnd_7103685 : Nat := 405289424792682725940917

theorem tailTrace_7103685 : CollatzResearch.WordTrace tailWord_7103685 prefixEnd_7103685 405289424792682725940917 := by
  unfold tailWord_7103685
  simp only [CollatzResearch.WordTrace]
  refine ⟨259092677269569932654304509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172728451513046621769536339 259092677269569932654304509)
  ·
    refine ⟨97159753976088724745364191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259092677269569932654304509 97159753976088724745364191)
    ·
      refine ⟨145739630964133087118046287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97159753976088724745364191 145739630964133087118046287)
      ·
        refine ⟨218609446446199630677069431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145739630964133087118046287 218609446446199630677069431)
        ·
          refine ⟨327914169669299446015604147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218609446446199630677069431 327914169669299446015604147)
          ·
            refine ⟨491871254503949169023406221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327914169669299446015604147 491871254503949169023406221)
            ·
              refine ⟨184451720438980938383777333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 491871254503949169023406221 184451720438980938383777333)
              ·
                refine ⟨17292348791154462973479125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 184451720438980938383777333 17292348791154462973479125)
                ·
                  refine ⟨405289424792682725940917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17292348791154462973479125 405289424792682725940917)
                  ·
                    rfl

theorem cell23_7103685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 5, 7].length) (baseStart_7103685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7103685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7103685 prefixEnd_7103685 := by exact prefixLift 7103685
  have htrace : WordTrace (prefixWord ++ tailWord_7103685) baseStart_7103685 baseEnd_7103685 := by
    simpa [prefixWord, tailWord_7103685, baseEnd_7103685] using wordTrace_append hprefix tailTrace_7103685
  have hstable : (prefixWord ++ tailWord_7103685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7103685).length < 2 ^ (prefixWord ++ tailWord_7103685).sum := by decide
  have hdescent : baseEnd_7103685 < baseStart_7103685 := by decide
  rcases family_descends (prefixWord ++ tailWord_7103685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7103730 : List Nat := [3, 2, 1, 3, 3, 2, 1, 2, 2, 2, 2]
def baseStart_7103730 : Nat := 118140960795 + 7103730 * 2 ^ 59
def prefixEnd_7103730 : Nat := 4983230072969 + 3 ^ 40 * 7103730 * 2
def baseEnd_7103730 : Nat := 3647627929763596857405547

theorem tailTrace_7103730 : CollatzResearch.WordTrace tailWord_7103730 prefixEnd_7103730 3647627929763596857405547 := by
  unfold tailWord_7103730
  simp only [CollatzResearch.WordTrace]
  refine ⟨64773579638601726334923161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172729545702937936893128429 64773579638601726334923161)
  ·
    refine ⟨48580184728951294751192371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64773579638601726334923161 48580184728951294751192371)
    ·
      refine ⟨72870277093426942126788557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48580184728951294751192371 72870277093426942126788557)
      ·
        refine ⟨27326353910035103297545709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72870277093426942126788557 27326353910035103297545709)
        ·
          refine ⟨10247382716263163736579641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27326353910035103297545709 10247382716263163736579641)
          ·
            refine ⟨7685537037197372802434731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10247382716263163736579641 7685537037197372802434731)
            ·
              refine ⟨11528305555796059203652097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7685537037197372802434731 11528305555796059203652097)
              ·
                refine ⟨8646229166847044402739073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11528305555796059203652097 8646229166847044402739073)
                ·
                  refine ⟨6484671875135283302054305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8646229166847044402739073 6484671875135283302054305)
                  ·
                    refine ⟨4863503906351462476540729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6484671875135283302054305 4863503906351462476540729)
                    ·
                      refine ⟨3647627929763596857405547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4863503906351462476540729 3647627929763596857405547)
                      ·
                        rfl

theorem cell23_7103730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 2, 2, 2, 2].length) (baseStart_7103730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7103730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7103730 prefixEnd_7103730 := by exact prefixLift 7103730
  have htrace : WordTrace (prefixWord ++ tailWord_7103730) baseStart_7103730 baseEnd_7103730 := by
    simpa [prefixWord, tailWord_7103730, baseEnd_7103730] using wordTrace_append hprefix tailTrace_7103730
  have hstable : (prefixWord ++ tailWord_7103730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7103730).length < 2 ^ (prefixWord ++ tailWord_7103730).sum := by decide
  have hdescent : baseEnd_7103730 < baseStart_7103730 := by decide
  rcases family_descends (prefixWord ++ tailWord_7103730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7103786 : List Nat := [3, 1, 4, 2, 1, 2, 1, 2, 2, 1, 4]
def baseStart_7103786 : Nat := 118140960795 + 7103786 * 2 ^ 59
def prefixEnd_7103786 : Nat := 4983230072969 + 3 ^ 40 * 7103786 * 2
def baseEnd_7103786 : Nat := 3647656684680248638305289

theorem tailTrace_7103786 : CollatzResearch.WordTrace tailWord_7103786 prefixEnd_7103786 3647656684680248638305289 := by
  unfold tailWord_7103786
  simp only [CollatzResearch.WordTrace]
  refine ⟨64774090260551006725932803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172730907361469351269154141 64774090260551006725932803)
  ·
    refine ⟨97161135390826510088899205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64774090260551006725932803 97161135390826510088899205)
    ·
      refine ⟨18217712885779970641668601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97161135390826510088899205 18217712885779970641668601)
      ·
        refine ⟨13663284664334977981251451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18217712885779970641668601 13663284664334977981251451)
        ·
          refine ⟨20494926996502466971877177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13663284664334977981251451 20494926996502466971877177)
          ·
            refine ⟨15371195247376850228907883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20494926996502466971877177 15371195247376850228907883)
            ·
              refine ⟨23056792871065275343361825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15371195247376850228907883 23056792871065275343361825)
              ·
                refine ⟨17292594653298956507521369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23056792871065275343361825 17292594653298956507521369)
                ·
                  refine ⟨12969445989974217380641027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17292594653298956507521369 12969445989974217380641027)
                  ·
                    refine ⟨19454168984961326070961541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12969445989974217380641027 19454168984961326070961541)
                    ·
                      refine ⟨3647656684680248638305289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19454168984961326070961541 3647656684680248638305289)
                      ·
                        rfl

theorem cell23_7103786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_7103786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7103786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7103786 prefixEnd_7103786 := by exact prefixLift 7103786
  have htrace : WordTrace (prefixWord ++ tailWord_7103786) baseStart_7103786 baseEnd_7103786 := by
    simpa [prefixWord, tailWord_7103786, baseEnd_7103786] using wordTrace_append hprefix tailTrace_7103786
  have hstable : (prefixWord ++ tailWord_7103786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7103786).length < 2 ^ (prefixWord ++ tailWord_7103786).sum := by decide
  have hdescent : baseEnd_7103786 < baseStart_7103786 := by decide
  rcases family_descends (prefixWord ++ tailWord_7103786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7103792 : List Nat := [2, 1, 1, 1, 2, 2, 4, 4, 6]
def baseStart_7103792 : Nat := 118140960795 + 7103792 * 2 ^ 59
def prefixEnd_7103792 : Nat := 4983230072969 + 3 ^ 40 * 7103792 * 2
def baseEnd_7103792 : Nat := 405295529507130623870029

theorem tailTrace_7103792 : CollatzResearch.WordTrace tailWord_7103792 prefixEnd_7103792 405295529507130623870029 := by
  unfold tailWord_7103792
  simp only [CollatzResearch.WordTrace]
  refine ⟨129548289940091144964224815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172731053253454859952299753 129548289940091144964224815)
  ·
    refine ⟨194322434910136717446337223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129548289940091144964224815 194322434910136717446337223)
    ·
      refine ⟨291483652365205076169505835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194322434910136717446337223 291483652365205076169505835)
      ·
        refine ⟨437225478547807614254258753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291483652365205076169505835 437225478547807614254258753)
        ·
          refine ⟨327919108910855710690694065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 437225478547807614254258753 327919108910855710690694065)
          ·
            refine ⟨245939331683141783018020549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 327919108910855710690694065 245939331683141783018020549)
            ·
              refine ⟨46113624690589084315878853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 245939331683141783018020549 46113624690589084315878853)
              ·
                refine ⟨8646304629485453309227285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46113624690589084315878853 8646304629485453309227285)
                ·
                  refine ⟨405295529507130623870029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8646304629485453309227285 405295529507130623870029)
                  ·
                    rfl

theorem cell23_7103792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 4, 6].length) (baseStart_7103792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7103792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7103792 prefixEnd_7103792 := by exact prefixLift 7103792
  have htrace : WordTrace (prefixWord ++ tailWord_7103792) baseStart_7103792 baseEnd_7103792 := by
    simpa [prefixWord, tailWord_7103792, baseEnd_7103792] using wordTrace_append hprefix tailTrace_7103792
  have hstable : (prefixWord ++ tailWord_7103792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7103792).length < 2 ^ (prefixWord ++ tailWord_7103792).sum := by decide
  have hdescent : baseEnd_7103792 < baseStart_7103792 := by decide
  rcases family_descends (prefixWord ++ tailWord_7103792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7103847 : List Nat := [1, 1, 5, 1, 5, 1, 2, 2, 1, 4]
def baseStart_7103847 : Nat := 118140960795 + 7103847 * 2 ^ 59
def prefixEnd_7103847 : Nat := 4983230072969 + 3 ^ 40 * 7103847 * 2
def baseEnd_7103847 : Nat := 1215896002333390966547503

theorem tailTrace_7103847 : CollatzResearch.WordTrace tailWord_7103847 prefixEnd_7103847 1215896002333390966547503 := by
  unfold tailWord_7103847
  simp only [CollatzResearch.WordTrace]
  refine ⟨259098585894983034321701795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172732390596655356214467863 259098585894983034321701795)
  ·
    refine ⟨388647878842474551482552693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259098585894983034321701795 388647878842474551482552693)
    ·
      refine ⟨36435738641481989201489315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 388647878842474551482552693 36435738641481989201489315)
      ·
        refine ⟨54653607962222983802233973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36435738641481989201489315 54653607962222983802233973)
        ·
          refine ⟨5123775746458404731459435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54653607962222983802233973 5123775746458404731459435)
          ·
            refine ⟨7685663619687607097189153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5123775746458404731459435 7685663619687607097189153)
            ·
              refine ⟨5764247714765705322891865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7685663619687607097189153 5764247714765705322891865)
              ·
                refine ⟨4323185786074278992168899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5764247714765705322891865 4323185786074278992168899)
                ·
                  refine ⟨6484778679111418488253349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4323185786074278992168899 6484778679111418488253349)
                  ·
                    refine ⟨1215896002333390966547503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6484778679111418488253349 1215896002333390966547503)
                    ·
                      rfl

theorem cell23_7103847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 2, 2, 1, 4].length) (baseStart_7103847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7103847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7103847 prefixEnd_7103847 := by exact prefixLift 7103847
  have htrace : WordTrace (prefixWord ++ tailWord_7103847) baseStart_7103847 baseEnd_7103847 := by
    simpa [prefixWord, tailWord_7103847, baseEnd_7103847] using wordTrace_append hprefix tailTrace_7103847
  have hstable : (prefixWord ++ tailWord_7103847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7103847).length < 2 ^ (prefixWord ++ tailWord_7103847).sum := by decide
  have hdescent : baseEnd_7103847 < baseStart_7103847 := by decide
  rcases family_descends (prefixWord ++ tailWord_7103847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7103869 : List Nat := [1, 4, 1, 1, 2, 2, 4, 1, 1, 6]
def baseStart_7103869 : Nat := 118140960795 + 7103869 * 2 ^ 59
def prefixEnd_7103869 : Nat := 4983230072969 + 3 ^ 40 * 7103869 * 2
def baseEnd_7103869 : Nat := 1215899767858190604522469

theorem tailTrace_7103869 : CollatzResearch.WordTrace tailWord_7103869 prefixEnd_7103869 1215899767858190604522469 := by
  unfold tailWord_7103869
  simp only [CollatzResearch.WordTrace]
  refine ⟨259099388300903332079002661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172732925533935554719335107 259099388300903332079002661)
  ·
    refine ⟨48581135306419374764812999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 259099388300903332079002661 48581135306419374764812999)
    ·
      refine ⟨72871702959629062147219499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48581135306419374764812999 72871702959629062147219499)
      ·
        refine ⟨109307554439443593220829249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72871702959629062147219499 109307554439443593220829249)
        ·
          refine ⟨81980665829582694915621937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109307554439443593220829249 81980665829582694915621937)
          ·
            refine ⟨61485499372187021186716453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81980665829582694915621937 61485499372187021186716453)
            ·
              refine ⟨11528531132285066472509335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61485499372187021186716453 11528531132285066472509335)
              ·
                refine ⟨17292796698427599708764003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11528531132285066472509335 17292796698427599708764003)
                ·
                  refine ⟨25939195047641399563146005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17292796698427599708764003 25939195047641399563146005)
                  ·
                    refine ⟨1215899767858190604522469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25939195047641399563146005 1215899767858190604522469)
                    ·
                      rfl

theorem cell23_7103869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 1, 1, 6].length) (baseStart_7103869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7103869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7103869 prefixEnd_7103869 := by exact prefixLift 7103869
  have htrace : WordTrace (prefixWord ++ tailWord_7103869) baseStart_7103869 baseEnd_7103869 := by
    simpa [prefixWord, tailWord_7103869, baseEnd_7103869] using wordTrace_append hprefix tailTrace_7103869
  have hstable : (prefixWord ++ tailWord_7103869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7103869).length < 2 ^ (prefixWord ++ tailWord_7103869).sum := by decide
  have hdescent : baseEnd_7103869 < baseStart_7103869 := by decide
  rcases family_descends (prefixWord ++ tailWord_7103869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7103872 : List Nat := [2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 6]
def baseStart_7103872 : Nat := 118140960795 + 7103872 * 2 ^ 59
def prefixEnd_7103872 : Nat := 4983230072969 + 3 ^ 40 * 7103872 * 2
def baseEnd_7103872 : Nat := 3647700844016535301829893

theorem tailTrace_7103872 : CollatzResearch.WordTrace tailWord_7103872 prefixEnd_7103872 3647700844016535301829893 := by
  unfold tailWord_7103872
  simp only [CollatzResearch.WordTrace]
  refine ⟨129549748859946231795680935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172732998479928309060907913 129549748859946231795680935)
  ·
    refine ⟨194324623289919347693521403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129549748859946231795680935 194324623289919347693521403)
    ·
      refine ⟨291486934934879021540282105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194324623289919347693521403 291486934934879021540282105)
      ·
        refine ⟨218615201201159266155211579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291486934934879021540282105 218615201201159266155211579)
        ·
          refine ⟨327922801801738899232817369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218615201201159266155211579 327922801801738899232817369)
          ·
            refine ⟨245942101351304174424613027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 327922801801738899232817369 245942101351304174424613027)
            ·
              refine ⟨368913152026956261636919541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245942101351304174424613027 368913152026956261636919541)
              ·
                refine ⟨34585608002527149528461207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 368913152026956261636919541 34585608002527149528461207)
                ·
                  refine ⟨51878412003790724292691811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34585608002527149528461207 51878412003790724292691811)
                  ·
                    refine ⟨77817618005686086439037717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51878412003790724292691811 77817618005686086439037717)
                    ·
                      refine ⟨3647700844016535301829893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77817618005686086439037717 3647700844016535301829893)
                      ·
                        rfl

theorem cell23_7103872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 6].length) (baseStart_7103872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7103872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7103872 prefixEnd_7103872 := by exact prefixLift 7103872
  have htrace : WordTrace (prefixWord ++ tailWord_7103872) baseStart_7103872 baseEnd_7103872 := by
    simpa [prefixWord, tailWord_7103872, baseEnd_7103872] using wordTrace_append hprefix tailTrace_7103872
  have hstable : (prefixWord ++ tailWord_7103872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7103872).length < 2 ^ (prefixWord ++ tailWord_7103872).sum := by decide
  have hdescent : baseEnd_7103872 < baseStart_7103872 := by decide
  rcases family_descends (prefixWord ++ tailWord_7103872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7103903 : List Nat := [1, 1, 2, 5, 1, 4, 1, 2, 2, 4]
def baseStart_7103903 : Nat := 118140960795 + 7103903 * 2 ^ 59
def prefixEnd_7103903 : Nat := 4983230072969 + 3 ^ 40 * 7103903 * 2
def baseEnd_7103903 : Nat := 1215905587305608226847417

theorem tailTrace_7103903 : CollatzResearch.WordTrace tailWord_7103903 prefixEnd_7103903 1215905587305608226847417 := by
  unfold tailWord_7103903
  simp only [CollatzResearch.WordTrace]
  refine ⟨259100628382780155885740363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172733752255186770590493575 259100628382780155885740363)
  ·
    refine ⟨388650942574170233828610545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259100628382780155885740363 388650942574170233828610545)
    ·
      refine ⟨291488206930627675371457909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 388650942574170233828610545 291488206930627675371457909)
      ·
        refine ⟨27327019399746344566074179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 291488206930627675371457909 27327019399746344566074179)
        ·
          refine ⟨40990529099619516849111269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27327019399746344566074179 40990529099619516849111269)
          ·
            refine ⟨7685724206178659409208363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40990529099619516849111269 7685724206178659409208363)
            ·
              refine ⟨11528586309267989113812545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7685724206178659409208363 11528586309267989113812545)
              ·
                refine ⟨8646439731950991835359409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11528586309267989113812545 8646439731950991835359409)
                ·
                  refine ⟨6484829798963243876519557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8646439731950991835359409 6484829798963243876519557)
                  ·
                    refine ⟨1215905587305608226847417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6484829798963243876519557 1215905587305608226847417)
                    ·
                      rfl

theorem cell23_7103903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 2, 2, 4].length) (baseStart_7103903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7103903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7103903 prefixEnd_7103903 := by exact prefixLift 7103903
  have htrace : WordTrace (prefixWord ++ tailWord_7103903) baseStart_7103903 baseEnd_7103903 := by
    simpa [prefixWord, tailWord_7103903, baseEnd_7103903] using wordTrace_append hprefix tailTrace_7103903
  have hstable : (prefixWord ++ tailWord_7103903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7103903).length < 2 ^ (prefixWord ++ tailWord_7103903).sum := by decide
  have hdescent : baseEnd_7103903 < baseStart_7103903 := by decide
  rcases family_descends (prefixWord ++ tailWord_7103903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7103936 : List Nat := [2, 1, 1, 2, 3, 1, 2, 3, 3, 3, 2]
def baseStart_7103936 : Nat := 118140960795 + 7103936 * 2 ^ 59
def prefixEnd_7103936 : Nat := 4983230072969 + 3 ^ 40 * 7103936 * 2
def baseEnd_7103936 : Nat := 3647733706778423051429599

theorem tailTrace_7103936 : CollatzResearch.WordTrace tailWord_7103936 prefixEnd_7103936 3647733706778423051429599 := by
  unfold tailWord_7103936
  simp only [CollatzResearch.WordTrace]
  refine ⟨129550915995830301260845831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172734554661107068347794441 129550915995830301260845831)
  ·
    refine ⟨194326373993745451891268747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129550915995830301260845831 194326373993745451891268747)
    ·
      refine ⟨291489560990618177836903121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194326373993745451891268747 291489560990618177836903121)
      ·
        refine ⟨218617170742963633377677341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291489560990618177836903121 218617170742963633377677341)
        ·
          refine ⟨81981439028611362516629003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218617170742963633377677341 81981439028611362516629003)
          ·
            refine ⟨122972158542917043774943505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81981439028611362516629003 122972158542917043774943505)
            ·
              refine ⟨92229118907187782831207629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122972158542917043774943505 92229118907187782831207629)
              ·
                refine ⟨34585919590195418561702861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92229118907187782831207629 34585919590195418561702861)
                ·
                  refine ⟨12969719846323281960638573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34585919590195418561702861 12969719846323281960638573)
                  ·
                    refine ⟨4863644942371230735239465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12969719846323281960638573 4863644942371230735239465)
                    ·
                      refine ⟨3647733706778423051429599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4863644942371230735239465 3647733706778423051429599)
                      ·
                        rfl

theorem cell23_7103936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 3, 3, 2].length) (baseStart_7103936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7103936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7103936 prefixEnd_7103936 := by exact prefixLift 7103936
  have htrace : WordTrace (prefixWord ++ tailWord_7103936) baseStart_7103936 baseEnd_7103936 := by
    simpa [prefixWord, tailWord_7103936, baseEnd_7103936] using wordTrace_append hprefix tailTrace_7103936
  have hstable : (prefixWord ++ tailWord_7103936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7103936).length < 2 ^ (prefixWord ++ tailWord_7103936).sum := by decide
  have hdescent : baseEnd_7103936 < baseStart_7103936 := by decide
  rcases family_descends (prefixWord ++ tailWord_7103936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7103938 : List Nat := [3, 5, 2, 1, 1, 2, 1, 3, 1, 1, 3]
def baseStart_7103938 : Nat := 118140960795 + 7103938 * 2 ^ 59
def prefixEnd_7103938 : Nat := 4983230072969 + 3 ^ 40 * 7103938 * 2
def baseEnd_7103938 : Nat := 3647734733739732043604591

theorem tailTrace_7103938 : CollatzResearch.WordTrace tailWord_7103938 prefixEnd_7103938 3647734733739732043604591 := by
  unfold tailWord_7103938
  simp only [CollatzResearch.WordTrace]
  refine ⟨64775476234413339215816117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172734603291768904575509645 64775476234413339215816117)
  ·
    refine ⟨6072700896976250551482761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64775476234413339215816117 6072700896976250551482761)
    ·
      refine ⟨4554525672732187913612071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6072700896976250551482761 4554525672732187913612071)
      ·
        refine ⟨6831788509098281870418107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4554525672732187913612071 6831788509098281870418107)
        ·
          refine ⟨10247682763647422805627161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6831788509098281870418107 10247682763647422805627161)
          ·
            refine ⟨7685762072735567104220371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10247682763647422805627161 7685762072735567104220371)
            ·
              refine ⟨11528643109103350656330557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7685762072735567104220371 11528643109103350656330557)
              ·
                refine ⟨4323241165913756496123959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11528643109103350656330557 4323241165913756496123959)
                ·
                  refine ⟨6484861748870634744185939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4323241165913756496123959 6484861748870634744185939)
                  ·
                    refine ⟨9727292623305952116278909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6484861748870634744185939 9727292623305952116278909)
                    ·
                      refine ⟨3647734733739732043604591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9727292623305952116278909 3647734733739732043604591)
                      ·
                        rfl

theorem cell23_7103938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_7103938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7103938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7103938 prefixEnd_7103938 := by exact prefixLift 7103938
  have htrace : WordTrace (prefixWord ++ tailWord_7103938) baseStart_7103938 baseEnd_7103938 := by
    simpa [prefixWord, tailWord_7103938, baseEnd_7103938] using wordTrace_append hprefix tailTrace_7103938
  have hstable : (prefixWord ++ tailWord_7103938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7103938).length < 2 ^ (prefixWord ++ tailWord_7103938).sum := by decide
  have hdescent : baseEnd_7103938 < baseStart_7103938 := by decide
  rcases family_descends (prefixWord ++ tailWord_7103938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7103986 : List Nat := [3, 2, 1, 4, 1, 1, 1, 2, 2, 1, 5]
def baseStart_7103986 : Nat := 118140960795 + 7103986 * 2 ^ 59
def prefixEnd_7103986 : Nat := 4983230072969 + 3 ^ 40 * 7103986 * 2
def baseEnd_7103986 : Nat := 3647759380811147855804369

theorem tailTrace_7103986 : CollatzResearch.WordTrace tailWord_7103986 prefixEnd_7103986 3647759380811147855804369 := by
  unfold tailWord_7103986
  simp only [CollatzResearch.WordTrace]
  refine ⟨64775913910369865265252953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172735770427652974040674541 64775913910369865265252953)
  ·
    refine ⟨48581935432777398948939715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64775913910369865265252953 48581935432777398948939715)
    ·
      refine ⟨72872903149166098423409573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48581935432777398948939715 72872903149166098423409573)
      ·
        refine ⟨13663669340468643454389295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72872903149166098423409573 13663669340468643454389295)
        ·
          refine ⟨20495504010702965181583943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13663669340468643454389295 20495504010702965181583943)
          ·
            refine ⟨30743256016054447772375915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20495504010702965181583943 30743256016054447772375915)
            ·
              refine ⟨46114884024081671658563873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30743256016054447772375915 46114884024081671658563873)
              ·
                refine ⟨34586163018061253743922905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46114884024081671658563873 34586163018061253743922905)
                ·
                  refine ⟨25939622263545940307942179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34586163018061253743922905 25939622263545940307942179)
                  ·
                    refine ⟨38909433395318910461913269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25939622263545940307942179 38909433395318910461913269)
                    ·
                      refine ⟨3647759380811147855804369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38909433395318910461913269 3647759380811147855804369)
                      ·
                        rfl

theorem cell23_7103986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_7103986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7103986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7103986 prefixEnd_7103986 := by exact prefixLift 7103986
  have htrace : WordTrace (prefixWord ++ tailWord_7103986) baseStart_7103986 baseEnd_7103986 := by
    simpa [prefixWord, tailWord_7103986, baseEnd_7103986] using wordTrace_append hprefix tailTrace_7103986
  have hstable : (prefixWord ++ tailWord_7103986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7103986).length < 2 ^ (prefixWord ++ tailWord_7103986).sum := by decide
  have hdescent : baseEnd_7103986 < baseStart_7103986 := by decide
  rcases family_descends (prefixWord ++ tailWord_7103986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7103999 : List Nat := [1, 1, 2, 2, 1, 2, 2, 1, 3, 5, 3]
def baseStart_7103999 : Nat := 118140960795 + 7103999 * 2 ^ 59
def prefixEnd_7103999 : Nat := 4983230072969 + 3 ^ 40 * 7103999 * 2
def baseEnd_7103999 : Nat := 3647766056059656304941809

theorem tailTrace_7103999 : CollatzResearch.WordTrace tailWord_7103999 prefixEnd_7103999 3647766056059656304941809 := by
  unfold tailWord_7103999
  simp only [CollatzResearch.WordTrace]
  refine ⟨259104129790432364281235051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172736086526954909520823367 259104129790432364281235051)
  ·
    refine ⟨388656194685648546421852577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259104129790432364281235051 388656194685648546421852577)
    ·
      refine ⟨291492146014236409816389433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 388656194685648546421852577 291492146014236409816389433)
      ·
        refine ⟨218619109510677307362292075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291492146014236409816389433 218619109510677307362292075)
        ·
          refine ⟨327928664266015961043438113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218619109510677307362292075 327928664266015961043438113)
          ·
            refine ⟨245946498199511970782578585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 327928664266015961043438113 245946498199511970782578585)
            ·
              refine ⟨184459873649633978086933939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 245946498199511970782578585 184459873649633978086933939)
              ·
                refine ⟨276689810474450967130400909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184459873649633978086933939 276689810474450967130400909)
                ·
                  refine ⟨103758678927919112673900341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 276689810474450967130400909 103758678927919112673900341)
                  ·
                    refine ⟨9727376149492416813178157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 103758678927919112673900341 9727376149492416813178157)
                    ·
                      refine ⟨3647766056059656304941809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9727376149492416813178157 3647766056059656304941809)
                      ·
                        rfl

theorem cell23_7103999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 5, 3].length) (baseStart_7103999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7103999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7103999 prefixEnd_7103999 := by exact prefixLift 7103999
  have htrace : WordTrace (prefixWord ++ tailWord_7103999) baseStart_7103999 baseEnd_7103999 := by
    simpa [prefixWord, tailWord_7103999, baseEnd_7103999] using wordTrace_append hprefix tailTrace_7103999
  have hstable : (prefixWord ++ tailWord_7103999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7103999).length < 2 ^ (prefixWord ++ tailWord_7103999).sum := by decide
  have hdescent : baseEnd_7103999 < baseStart_7103999 := by decide
  rcases family_descends (prefixWord ++ tailWord_7103999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7104053 : List Nat := [1, 3, 3, 1, 1, 5, 1, 1, 2, 5]
def baseStart_7104053 : Nat := 118140960795 + 7104053 * 2 ^ 59
def prefixEnd_7104053 : Nat := 4983230072969 + 3 ^ 40 * 7104053 * 2
def baseEnd_7104053 : Nat := 1215931261338333031222187

theorem tailTrace_7104053 : CollatzResearch.WordTrace tailWord_7104053 prefixEnd_7104053 1215931261338333031222187 := by
  unfold tailWord_7104053
  simp only [CollatzResearch.WordTrace]
  refine ⟨259106099332236731503700813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172737399554824487669133875 259106099332236731503700813)
  ·
    refine ⟨97164787249588774313887805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259106099332236731503700813 97164787249588774313887805)
    ·
      refine ⟨36436795218595790367707927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97164787249588774313887805 36436795218595790367707927)
      ·
        refine ⟨54655192827893685551561891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36436795218595790367707927 54655192827893685551561891)
        ·
          refine ⟨81982789241840528327342837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54655192827893685551561891 81982789241840528327342837)
          ·
            refine ⟨7685886491422549530688391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81982789241840528327342837 7685886491422549530688391)
            ·
              refine ⟨11528829737133824296032587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7685886491422549530688391 11528829737133824296032587)
              ·
                refine ⟨17293244605700736444048881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11528829737133824296032587 17293244605700736444048881)
                ·
                  refine ⟨12969933454275552333036661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17293244605700736444048881 12969933454275552333036661)
                  ·
                    refine ⟨1215931261338333031222187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12969933454275552333036661 1215931261338333031222187)
                    ·
                      rfl

theorem cell23_7104053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 1, 2, 5].length) (baseStart_7104053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7104053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7104053 prefixEnd_7104053 := by exact prefixLift 7104053
  have htrace : WordTrace (prefixWord ++ tailWord_7104053) baseStart_7104053 baseEnd_7104053 := by
    simpa [prefixWord, tailWord_7104053, baseEnd_7104053] using wordTrace_append hprefix tailTrace_7104053
  have hstable : (prefixWord ++ tailWord_7104053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7104053).length < 2 ^ (prefixWord ++ tailWord_7104053).sum := by decide
  have hdescent : baseEnd_7104053 < baseStart_7104053 := by decide
  rcases family_descends (prefixWord ++ tailWord_7104053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7104056 : List Nat := [2, 1, 2, 1, 4, 3, 1, 1, 1, 3, 4]
def baseStart_7104056 : Nat := 118140960795 + 7104056 * 2 ^ 59
def prefixEnd_7104056 : Nat := 4983230072969 + 3 ^ 40 * 7104056 * 2
def baseEnd_7104056 : Nat := 3647795324456962581929047

theorem tailTrace_7104056 : CollatzResearch.WordTrace tailWord_7104056 prefixEnd_7104056 3647795324456962581929047 := by
  unfold tailWord_7104056
  simp only [CollatzResearch.WordTrace]
  refine ⟨129553104375612931508030011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172737472500817242010706681 129553104375612931508030011)
  ·
    refine ⟨194329656563419397262045017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129553104375612931508030011 194329656563419397262045017)
    ·
      refine ⟨145747242422564547946533763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194329656563419397262045017 145747242422564547946533763)
      ·
        refine ⟨218620863633846821919800645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145747242422564547946533763 218620863633846821919800645)
        ·
          refine ⟨40991411931346279109962621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 218620863633846821919800645 40991411931346279109962621)
          ·
            refine ⟨15371779474254854666235983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40991411931346279109962621 15371779474254854666235983)
            ·
              refine ⟨23057669211382281999353975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15371779474254854666235983 23057669211382281999353975)
              ·
                refine ⟨34586503817073422999030963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23057669211382281999353975 34586503817073422999030963)
                ·
                  refine ⟨51879755725610134498546445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34586503817073422999030963 51879755725610134498546445)
                  ·
                    refine ⟨19454908397103800436954917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51879755725610134498546445 19454908397103800436954917)
                    ·
                      refine ⟨3647795324456962581929047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19454908397103800436954917 3647795324456962581929047)
                      ·
                        rfl

theorem cell23_7104056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 1, 3, 4].length) (baseStart_7104056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7104056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7104056 prefixEnd_7104056 := by exact prefixLift 7104056
  have htrace : WordTrace (prefixWord ++ tailWord_7104056) baseStart_7104056 baseEnd_7104056 := by
    simpa [prefixWord, tailWord_7104056, baseEnd_7104056] using wordTrace_append hprefix tailTrace_7104056
  have hstable : (prefixWord ++ tailWord_7104056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7104056).length < 2 ^ (prefixWord ++ tailWord_7104056).sum := by decide
  have hdescent : baseEnd_7104056 < baseStart_7104056 := by decide
  rcases family_descends (prefixWord ++ tailWord_7104056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7104069 : List Nat := [1, 3, 1, 1, 1, 4, 1, 1, 1, 3, 6]
def baseStart_7104069 : Nat := 118140960795 + 7104069 * 2 ^ 59
def prefixEnd_7104069 : Nat := 4983230072969 + 3 ^ 40 * 7104069 * 2
def baseEnd_7104069 : Nat := 3647801999705471031066487

theorem tailTrace_7104069 : CollatzResearch.WordTrace tailWord_7104069 prefixEnd_7104069 3647801999705471031066487 := by
  unfold tailWord_7104069
  simp only [CollatzResearch.WordTrace]
  refine ⟨259106682900178766236283261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172737788600119177490855507 259106682900178766236283261)
  ·
    refine ⟨97165006087567037338606223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259106682900178766236283261 97165006087567037338606223)
    ·
      refine ⟨145747509131350556007909335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97165006087567037338606223 145747509131350556007909335)
      ·
        refine ⟨218621263697025834011864003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145747509131350556007909335 218621263697025834011864003)
        ·
          refine ⟨327931895545538751017796005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218621263697025834011864003 327931895545538751017796005)
          ·
            refine ⟨61487230414788515815836751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 327931895545538751017796005 61487230414788515815836751)
            ·
              refine ⟨92230845622182773723755127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61487230414788515815836751 92230845622182773723755127)
              ·
                refine ⟨138346268433274160585632691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92230845622182773723755127 138346268433274160585632691)
                ·
                  refine ⟨207519402649911240878449037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138346268433274160585632691 207519402649911240878449037)
                  ·
                    refine ⟨77819775993716715329418389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 207519402649911240878449037 77819775993716715329418389)
                    ·
                      refine ⟨3647801999705471031066487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77819775993716715329418389 3647801999705471031066487)
                      ·
                        rfl

theorem cell23_7104069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 3, 6].length) (baseStart_7104069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7104069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7104069 prefixEnd_7104069 := by exact prefixLift 7104069
  have htrace : WordTrace (prefixWord ++ tailWord_7104069) baseStart_7104069 baseEnd_7104069 := by
    simpa [prefixWord, tailWord_7104069, baseEnd_7104069] using wordTrace_append hprefix tailTrace_7104069
  have hstable : (prefixWord ++ tailWord_7104069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7104069).length < 2 ^ (prefixWord ++ tailWord_7104069).sum := by decide
  have hdescent : baseEnd_7104069 < baseStart_7104069 := by decide
  rcases family_descends (prefixWord ++ tailWord_7104069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7104117 : List Nat := [1, 3, 4, 2, 1, 1, 3, 3, 1, 4]
def baseStart_7104117 : Nat := 118140960795 + 7104117 * 2 ^ 59
def prefixEnd_7104117 : Nat := 4983230072969 + 3 ^ 40 * 7104117 * 2
def baseEnd_7104117 : Nat := 1215942215592295614422089

theorem tailTrace_7104117 : CollatzResearch.WordTrace tailWord_7104117 prefixEnd_7104117 1215942215592295614422089 := by
  unfold tailWord_7104117
  simp only [CollatzResearch.WordTrace]
  refine ⟨259108433604004870434030605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172738955736003246956020403 259108433604004870434030605)
  ·
    refine ⟨97165662601501826412761477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259108433604004870434030605 97165662601501826412761477)
    ·
      refine ⟨18218561737781592452392777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97165662601501826412761477 18218561737781592452392777)
      ·
        refine ⟨13663921303336194339294583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18218561737781592452392777 13663921303336194339294583)
        ·
          refine ⟨20495881955004291508941875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13663921303336194339294583 20495881955004291508941875)
          ·
            refine ⟨30743822932506437263412813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20495881955004291508941875 30743822932506437263412813)
            ·
              refine ⟨11528933599689913973779805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30743822932506437263412813 11528933599689913973779805)
              ·
                refine ⟨4323350099883717740167427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11528933599689913973779805 4323350099883717740167427)
                ·
                  refine ⟨6485025149825576610251141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4323350099883717740167427 6485025149825576610251141)
                  ·
                    refine ⟨1215942215592295614422089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6485025149825576610251141 1215942215592295614422089)
                    ·
                      rfl

theorem cell23_7104117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_7104117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7104117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7104117 prefixEnd_7104117 := by exact prefixLift 7104117
  have htrace : WordTrace (prefixWord ++ tailWord_7104117) baseStart_7104117 baseEnd_7104117 := by
    simpa [prefixWord, tailWord_7104117, baseEnd_7104117] using wordTrace_append hprefix tailTrace_7104117
  have hstable : (prefixWord ++ tailWord_7104117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7104117).length < 2 ^ (prefixWord ++ tailWord_7104117).sum := by decide
  have hdescent : baseEnd_7104117 < baseStart_7104117 := by decide
  rcases family_descends (prefixWord ++ tailWord_7104117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7104160 : List Nat := [2, 1, 1, 4, 3, 3, 1, 2, 1, 5]
def baseStart_7104160 : Nat := 118140960795 + 7104160 * 2 ^ 59
def prefixEnd_7104160 : Nat := 4983230072969 + 3 ^ 40 * 7104160 * 2
def baseEnd_7104160 : Nat := 1215949575481676725009523

theorem tailTrace_7104160 : CollatzResearch.WordTrace tailWord_7104160 prefixEnd_7104160 1215949575481676725009523 := by
  unfold tailWord_7104160
  simp only [CollatzResearch.WordTrace]
  refine ⟨129555000971424544388922967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172740001295232725851897289 129555000971424544388922967)
  ·
    refine ⟨194332501457136816583384451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129555000971424544388922967 194332501457136816583384451)
    ·
      refine ⟨291498752185705224875076677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194332501457136816583384451 291498752185705224875076677)
      ·
        refine ⟨54656016034819729664076877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 291498752185705224875076677 54656016034819729664076877)
        ·
          refine ⟨20496006013057398624028829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54656016034819729664076877 20496006013057398624028829)
          ·
            refine ⟨7686002254896524484010811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20496006013057398624028829 7686002254896524484010811)
            ·
              refine ⟨11529003382344786726016217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7686002254896524484010811 11529003382344786726016217)
              ·
                refine ⟨8646752536758590044512163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11529003382344786726016217 8646752536758590044512163)
                ·
                  refine ⟨12970128805137885066768245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8646752536758590044512163 12970128805137885066768245)
                  ·
                    refine ⟨1215949575481676725009523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12970128805137885066768245 1215949575481676725009523)
                    ·
                      rfl

theorem cell23_7104160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 2, 1, 5].length) (baseStart_7104160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7104160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7104160 prefixEnd_7104160 := by exact prefixLift 7104160
  have htrace : WordTrace (prefixWord ++ tailWord_7104160) baseStart_7104160 baseEnd_7104160 := by
    simpa [prefixWord, tailWord_7104160, baseEnd_7104160] using wordTrace_append hprefix tailTrace_7104160
  have hstable : (prefixWord ++ tailWord_7104160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7104160).length < 2 ^ (prefixWord ++ tailWord_7104160).sum := by decide
  have hdescent : baseEnd_7104160 < baseStart_7104160 := by decide
  rcases family_descends (prefixWord ++ tailWord_7104160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7104173 : List Nat := [1, 5, 2, 1, 1, 1, 3, 2, 1, 6]
def baseStart_7104173 : Nat := 118140960795 + 7104173 * 2 ^ 59
def prefixEnd_7104173 : Nat := 4983230072969 + 3 ^ 40 * 7104173 * 2
def baseEnd_7104173 : Nat := 1215951800564512874722003

theorem tailTrace_7104173 : CollatzResearch.WordTrace tailWord_7104173 prefixEnd_7104173 1215951800564512874722003 := by
  unfold tailWord_7104173
  simp only [CollatzResearch.WordTrace]
  refine ⟨259110476091801991998069173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172740317394534661332046115 259110476091801991998069173)
  ·
    refine ⟨24291607133606436749818985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 259110476091801991998069173 24291607133606436749818985)
    ·
      refine ⟨18218705350204827562364239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24291607133606436749818985 18218705350204827562364239)
      ·
        refine ⟨27328058025307241343546359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18218705350204827562364239 27328058025307241343546359)
        ·
          refine ⟨40992087037960862015319539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27328058025307241343546359 40992087037960862015319539)
          ·
            refine ⟨61488130556941293022979309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40992087037960862015319539 61488130556941293022979309)
            ·
              refine ⟨23058048958852984883617241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61488130556941293022979309 23058048958852984883617241)
              ·
                refine ⟨17293536719139738662712931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23058048958852984883617241 17293536719139738662712931)
                ·
                  refine ⟨25940305078709607994069397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17293536719139738662712931 25940305078709607994069397)
                  ·
                    refine ⟨1215951800564512874722003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25940305078709607994069397 1215951800564512874722003)
                    ·
                      rfl

theorem cell23_7104173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_7104173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7104173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7104173 prefixEnd_7104173 := by exact prefixLift 7104173
  have htrace : WordTrace (prefixWord ++ tailWord_7104173) baseStart_7104173 baseEnd_7104173 := by
    simpa [prefixWord, tailWord_7104173, baseEnd_7104173] using wordTrace_append hprefix tailTrace_7104173
  have hstable : (prefixWord ++ tailWord_7104173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7104173).length < 2 ^ (prefixWord ++ tailWord_7104173).sum := by decide
  have hdescent : baseEnd_7104173 < baseStart_7104173 := by decide
  rcases family_descends (prefixWord ++ tailWord_7104173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7104176 : List Nat := [2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 4]
def baseStart_7104176 : Nat := 118140960795 + 7104176 * 2 ^ 59
def prefixEnd_7104176 : Nat := 4983230072969 + 3 ^ 40 * 7104176 * 2
def baseEnd_7104176 : Nat := 3647856942135502112428495

theorem tailTrace_7104176 : CollatzResearch.WordTrace tailWord_7104176 prefixEnd_7104176 3647856942135502112428495 := by
  unfold tailWord_7104176
  simp only [CollatzResearch.WordTrace]
  refine ⟨129555292755395561755214191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172740390340527415673618921 129555292755395561755214191)
  ·
    refine ⟨194332939133093342632821287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129555292755395561755214191 194332939133093342632821287)
    ·
      refine ⟨291499408699640013949231931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194332939133093342632821287 291499408699640013949231931)
      ·
        refine ⟨437249113049460020923847897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291499408699640013949231931 437249113049460020923847897)
        ·
          refine ⟨327936834787095015692885923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 437249113049460020923847897 327936834787095015692885923)
          ·
            refine ⟨491905252180642523539328885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327936834787095015692885923 491905252180642523539328885)
            ·
              refine ⟨46116117391935236581812083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 491905252180642523539328885 46116117391935236581812083)
              ·
                refine ⟨69174176087902854872718125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46116117391935236581812083 69174176087902854872718125)
                ·
                  refine ⟨25940316032963570577269297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69174176087902854872718125 25940316032963570577269297)
                  ·
                    refine ⟨19455237024722677932951973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25940316032963570577269297 19455237024722677932951973)
                    ·
                      refine ⟨3647856942135502112428495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19455237024722677932951973 3647856942135502112428495)
                      ·
                        rfl

theorem cell23_7104176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 4].length) (baseStart_7104176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7104176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7104176 prefixEnd_7104176 := by exact prefixLift 7104176
  have htrace : WordTrace (prefixWord ++ tailWord_7104176) baseStart_7104176 baseEnd_7104176 := by
    simpa [prefixWord, tailWord_7104176, baseEnd_7104176] using wordTrace_append hprefix tailTrace_7104176
  have hstable : (prefixWord ++ tailWord_7104176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7104176).length < 2 ^ (prefixWord ++ tailWord_7104176).sum := by decide
  have hdescent : baseEnd_7104176 < baseStart_7104176 := by decide
  rcases family_descends (prefixWord ++ tailWord_7104176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7104183 : List Nat := [1, 1, 3, 1, 5, 1, 3, 1, 1, 1, 5]
def baseStart_7104183 : Nat := 118140960795 + 7104183 * 2 ^ 59
def prefixEnd_7104183 : Nat := 4983230072969 + 3 ^ 40 * 7104183 * 2
def baseEnd_7104183 : Nat := 3647860536500083585040963

theorem tailTrace_7104183 : CollatzResearch.WordTrace tailWord_7104183 prefixEnd_7104183 3647860536500083585040963 := by
  unfold tailWord_7104183
  simp only [CollatzResearch.WordTrace]
  refine ⟨259110840821765763705933203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172740560547843842470622135 259110840821765763705933203)
  ·
    refine ⟨388666261232648645558899805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259110840821765763705933203 388666261232648645558899805)
    ·
      refine ⟨145749847962243242084587427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 388666261232648645558899805 145749847962243242084587427)
      ·
        refine ⟨218624771943364863126881141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145749847962243242084587427 218624771943364863126881141)
        ·
          refine ⟨20496072369690455918145107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 218624771943364863126881141 20496072369690455918145107)
          ·
            refine ⟨30744108554535683877217661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20496072369690455918145107 30744108554535683877217661)
            ·
              refine ⟨11529040707950881453956623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30744108554535683877217661 11529040707950881453956623)
              ·
                refine ⟨17293561061926322180934935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11529040707950881453956623 17293561061926322180934935)
                ·
                  refine ⟨25940341592889483271402403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17293561061926322180934935 25940341592889483271402403)
                  ·
                    refine ⟨38910512389334224907103605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25940341592889483271402403 38910512389334224907103605)
                    ·
                      refine ⟨3647860536500083585040963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38910512389334224907103605 3647860536500083585040963)
                      ·
                        rfl

theorem cell23_7104183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 1, 1, 1, 5].length) (baseStart_7104183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7104183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7104183 prefixEnd_7104183 := by exact prefixLift 7104183
  have htrace : WordTrace (prefixWord ++ tailWord_7104183) baseStart_7104183 baseEnd_7104183 := by
    simpa [prefixWord, tailWord_7104183, baseEnd_7104183] using wordTrace_append hprefix tailTrace_7104183
  have hstable : (prefixWord ++ tailWord_7104183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7104183).length < 2 ^ (prefixWord ++ tailWord_7104183).sum := by decide
  have hdescent : baseEnd_7104183 < baseStart_7104183 := by decide
  rcases family_descends (prefixWord ++ tailWord_7104183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7104190 : List Nat := [4, 2, 1, 1, 2, 2, 1, 4, 2, 4]
def baseStart_7104190 : Nat := 118140960795 + 7104190 * 2 ^ 59
def prefixEnd_7104190 : Nat := 4983230072969 + 3 ^ 40 * 7104190 * 2
def baseEnd_7104190 : Nat := 1215954710288221685884477

theorem tailTrace_7104190 : CollatzResearch.WordTrace tailWord_7104190 prefixEnd_7104190 1215954710288221685884477 := by
  unfold tailWord_7104190
  simp only [CollatzResearch.WordTrace]
  refine ⟨32388887016592550487679753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172740730755160269267625349 32388887016592550487679753)
  ·
    refine ⟨24291665262444412865759815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32388887016592550487679753 24291665262444412865759815)
    ·
      refine ⟨36437497893666619298639723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24291665262444412865759815 36437497893666619298639723)
      ·
        refine ⟨54656246840499928947959585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36437497893666619298639723 54656246840499928947959585)
        ·
          refine ⟨40992185130374946710969689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54656246840499928947959585 40992185130374946710969689)
          ·
            refine ⟨30744138847781210033227267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40992185130374946710969689 30744138847781210033227267)
            ·
              refine ⟨46116208271671815049840901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30744138847781210033227267 46116208271671815049840901)
              ·
                refine ⟨8646789050938465321845169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46116208271671815049840901 8646789050938465321845169)
                ·
                  refine ⟨6485091788203848991383877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8646789050938465321845169 6485091788203848991383877)
                  ·
                    refine ⟨1215954710288221685884477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6485091788203848991383877 1215954710288221685884477)
                    ·
                      rfl

theorem cell23_7104190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 4, 2, 4].length) (baseStart_7104190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7104190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7104190 prefixEnd_7104190 := by exact prefixLift 7104190
  have htrace : WordTrace (prefixWord ++ tailWord_7104190) baseStart_7104190 baseEnd_7104190 := by
    simpa [prefixWord, tailWord_7104190, baseEnd_7104190] using wordTrace_append hprefix tailTrace_7104190
  have hstable : (prefixWord ++ tailWord_7104190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7104190).length < 2 ^ (prefixWord ++ tailWord_7104190).sum := by decide
  have hdescent : baseEnd_7104190 < baseStart_7104190 := by decide
  rcases family_descends (prefixWord ++ tailWord_7104190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7104197 : List Nat := [1, 3, 1, 1, 1, 1, 2, 8, 1, 2, 2]
def baseStart_7104197 : Nat := 118140960795 + 7104197 * 2 ^ 59
def prefixEnd_7104197 : Nat := 4983230072969 + 3 ^ 40 * 7104197 * 2
def baseEnd_7104197 : Nat := 3647867725229246530265899

theorem tailTrace_7104197 : CollatzResearch.WordTrace tailWord_7104197 prefixEnd_7104197 3647867725229246530265899 := by
  unfold tailWord_7104197
  simp only [CollatzResearch.WordTrace]
  refine ⟨259111351443715044096942845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172740900962476696064628563 259111351443715044096942845)
  ·
    refine ⟨97166756791393141536353567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259111351443715044096942845 97166756791393141536353567)
    ·
      refine ⟨145750135187089712304530351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97166756791393141536353567 145750135187089712304530351)
      ·
        refine ⟨218625202780634568456795527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145750135187089712304530351 218625202780634568456795527)
        ·
          refine ⟨327937804170951852685193291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218625202780634568456795527 327937804170951852685193291)
          ·
            refine ⟨491906706256427779027789937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327937804170951852685193291 491906706256427779027789937)
            ·
              refine ⟨368930029692320834270842453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 491906706256427779027789937 368930029692320834270842453)
              ·
                refine ⟨4323398785456884776611435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 368930029692320834270842453 4323398785456884776611435)
                ·
                  refine ⟨6485098178185327164917153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4323398785456884776611435 6485098178185327164917153)
                  ·
                    refine ⟨4863823633638995373687865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6485098178185327164917153 4863823633638995373687865)
                    ·
                      refine ⟨3647867725229246530265899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4863823633638995373687865 3647867725229246530265899)
                      ·
                        rfl

theorem cell23_7104197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 8, 1, 2, 2].length) (baseStart_7104197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7104197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7104197 prefixEnd_7104197 := by exact prefixLift 7104197
  have htrace : WordTrace (prefixWord ++ tailWord_7104197) baseStart_7104197 baseEnd_7104197 := by
    simpa [prefixWord, tailWord_7104197, baseEnd_7104197] using wordTrace_append hprefix tailTrace_7104197
  have hstable : (prefixWord ++ tailWord_7104197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7104197).length < 2 ^ (prefixWord ++ tailWord_7104197).sum := by decide
  have hdescent : baseEnd_7104197 < baseStart_7104197 := by decide
  rcases family_descends (prefixWord ++ tailWord_7104197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7104210 : List Nat := [3, 2, 2, 2, 2, 2, 2, 1, 1, 2, 4]
def baseStart_7104210 : Nat := 118140960795 + 7104210 * 2 ^ 59
def prefixEnd_7104210 : Nat := 4983230072969 + 3 ^ 40 * 7104210 * 2
def baseEnd_7104210 : Nat := 3647874400477754979403339

theorem tailTrace_7104210 : CollatzResearch.WordTrace tailWord_7104210 prefixEnd_7104210 3647874400477754979403339 := by
  unfold tailWord_7104210
  simp only [CollatzResearch.WordTrace]
  refine ⟨64777956398166986829291521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172741217061778631544777389 64777956398166986829291521)
  ·
    refine ⟨48583467298625240121968641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64777956398166986829291521 48583467298625240121968641)
    ·
      refine ⟨36437600473968930091476481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48583467298625240121968641 36437600473968930091476481)
      ·
        refine ⟨27328200355476697568607361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36437600473968930091476481 27328200355476697568607361)
        ·
          refine ⟨20496150266607523176455521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27328200355476697568607361 20496150266607523176455521)
          ·
            refine ⟨15372112699955642382341641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20496150266607523176455521 15372112699955642382341641)
            ·
              refine ⟨11529084524966731786756231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15372112699955642382341641 11529084524966731786756231)
              ·
                refine ⟨17293626787450097680134347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11529084524966731786756231 17293626787450097680134347)
                ·
                  refine ⟨25940440181175146520201521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17293626787450097680134347 25940440181175146520201521)
                  ·
                    refine ⟨19455330135881359890151141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25940440181175146520201521 19455330135881359890151141)
                    ·
                      refine ⟨3647874400477754979403339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19455330135881359890151141 3647874400477754979403339)
                      ·
                        rfl

theorem cell23_7104210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_7104210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7104210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7104210 prefixEnd_7104210 := by exact prefixLift 7104210
  have htrace : WordTrace (prefixWord ++ tailWord_7104210) baseStart_7104210 baseEnd_7104210 := by
    simpa [prefixWord, tailWord_7104210, baseEnd_7104210] using wordTrace_append hprefix tailTrace_7104210
  have hstable : (prefixWord ++ tailWord_7104210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7104210).length < 2 ^ (prefixWord ++ tailWord_7104210).sum := by decide
  have hdescent : baseEnd_7104210 < baseStart_7104210 := by decide
  rcases family_descends (prefixWord ++ tailWord_7104210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7104216 : List Nat := [2, 1, 2, 2, 3, 1, 1, 2, 2, 7]
def baseStart_7104216 : Nat := 118140960795 + 7104216 * 2 ^ 59
def prefixEnd_7104216 : Nat := 4983230072969 + 3 ^ 40 * 7104216 * 2
def baseEnd_7104216 : Nat := 1215959160453893985309437

theorem tailTrace_7104216 : CollatzResearch.WordTrace tailWord_7104216 prefixEnd_7104216 1215959160453893985309437 := by
  unfold tailWord_7104216
  simp only [CollatzResearch.WordTrace]
  refine ⟨129556022215323105170942251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172741362953764140227923001 129556022215323105170942251)
  ·
    refine ⟨194334033322984657756413377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129556022215323105170942251 194334033322984657756413377)
    ·
      refine ⟨145750524992238493317310033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194334033322984657756413377 145750524992238493317310033)
      ·
        refine ⟨109312893744178869987982525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145750524992238493317310033 109312893744178869987982525)
        ·
          refine ⟨40992335154067076245493447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109312893744178869987982525 40992335154067076245493447)
          ·
            refine ⟨61488502731100614368240171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40992335154067076245493447 61488502731100614368240171)
            ·
              refine ⟨92232754096650921552360257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61488502731100614368240171 92232754096650921552360257)
              ·
                refine ⟨69174565572488191164270193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92232754096650921552360257 69174565572488191164270193)
                ·
                  refine ⟨51880924179366143373202645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69174565572488191164270193 51880924179366143373202645)
                  ·
                    refine ⟨1215959160453893985309437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51880924179366143373202645 1215959160453893985309437)
                    ·
                      rfl

theorem cell23_7104216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 2, 7].length) (baseStart_7104216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7104216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7104216 prefixEnd_7104216 := by exact prefixLift 7104216
  have htrace : WordTrace (prefixWord ++ tailWord_7104216) baseStart_7104216 baseEnd_7104216 := by
    simpa [prefixWord, tailWord_7104216, baseEnd_7104216] using wordTrace_append hprefix tailTrace_7104216
  have hstable : (prefixWord ++ tailWord_7104216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7104216).length < 2 ^ (prefixWord ++ tailWord_7104216).sum := by decide
  have hdescent : baseEnd_7104216 < baseStart_7104216 := by decide
  rcases family_descends (prefixWord ++ tailWord_7104216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7104231 : List Nat := [1, 1, 5, 4, 2, 1, 2, 1, 1, 1, 4]
def baseStart_7104231 : Nat := 118140960795 + 7104231 * 2 ^ 59
def prefixEnd_7104231 : Nat := 4983230072969 + 3 ^ 40 * 7104231 * 2
def baseEnd_7104231 : Nat := 3647885183571499397240743

theorem tailTrace_7104231 : CollatzResearch.WordTrace tailWord_7104231 prefixEnd_7104231 3647885183571499397240743 := by
  unfold tailWord_7104231
  simp only [CollatzResearch.WordTrace]
  refine ⟨259112591525591867903680547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172741727683727911935787031 259112591525591867903680547)
  ·
    refine ⟨388668887288387801855520821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259112591525591867903680547 388668887288387801855520821)
    ·
      refine ⟨36437708183286356423955077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 388668887288387801855520821 36437708183286356423955077)
      ·
        refine ⟨6832070284366191829491577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36437708183286356423955077 6832070284366191829491577)
        ·
          refine ⟨5124052713274643872118683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6832070284366191829491577 5124052713274643872118683)
          ·
            refine ⟨7686079069911965808178025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5124052713274643872118683 7686079069911965808178025)
            ·
              refine ⟨5764559302433974356133519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7686079069911965808178025 5764559302433974356133519)
              ·
                refine ⟨8646838953650961534200279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5764559302433974356133519 8646838953650961534200279)
                ·
                  refine ⟨12970258430476442301300419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8646838953650961534200279 12970258430476442301300419)
                  ·
                    refine ⟨19455387645714663451950629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12970258430476442301300419 19455387645714663451950629)
                    ·
                      refine ⟨3647885183571499397240743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19455387645714663451950629 3647885183571499397240743)
                      ·
                        rfl

theorem cell23_7104231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_7104231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7104231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7104231 prefixEnd_7104231 := by exact prefixLift 7104231
  have htrace : WordTrace (prefixWord ++ tailWord_7104231) baseStart_7104231 baseEnd_7104231 := by
    simpa [prefixWord, tailWord_7104231, baseEnd_7104231] using wordTrace_append hprefix tailTrace_7104231
  have hstable : (prefixWord ++ tailWord_7104231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7104231).length < 2 ^ (prefixWord ++ tailWord_7104231).sum := by decide
  have hdescent : baseEnd_7104231 < baseStart_7104231 := by decide
  rcases family_descends (prefixWord ++ tailWord_7104231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7104256 : List Nat := [2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 5]
def baseStart_7104256 : Nat := 118140960795 + 7104256 * 2 ^ 59
def prefixEnd_7104256 : Nat := 4983230072969 + 3 ^ 40 * 7104256 * 2
def baseEnd_7104256 : Nat := 3647898020587861799428127

theorem tailTrace_7104256 : CollatzResearch.WordTrace tailWord_7104256 prefixEnd_7104256 3647898020587861799428127 := by
  unfold tailWord_7104256
  simp only [CollatzResearch.WordTrace]
  refine ⟨129556751675250648586670311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172742335567000864782227081 129556751675250648586670311)
  ·
    refine ⟨194335127512875972880005467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129556751675250648586670311 194335127512875972880005467)
    ·
      refine ⟨291502691269313959320008201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194335127512875972880005467 291502691269313959320008201)
      ·
        refine ⟨218627018451985469490006151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291502691269313959320008201 218627018451985469490006151)
        ·
          refine ⟨327940527677978204235009227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218627018451985469490006151 327940527677978204235009227)
          ·
            refine ⟨491910791516967306352513841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327940527677978204235009227 491910791516967306352513841)
            ·
              refine ⟨368933093637725479764385381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 491910791516967306352513841 368933093637725479764385381)
              ·
                refine ⟨69174955057073527455822259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 368933093637725479764385381 69174955057073527455822259)
                ·
                  refine ⟨103762432585610291183733389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69174955057073527455822259 103762432585610291183733389)
                  ·
                    refine ⟨38910912219603859193900021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 103762432585610291183733389 38910912219603859193900021)
                    ·
                      refine ⟨3647898020587861799428127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38910912219603859193900021 3647898020587861799428127)
                      ·
                        rfl

theorem cell23_7104256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 5].length) (baseStart_7104256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7104256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7104256 prefixEnd_7104256 := by exact prefixLift 7104256
  have htrace : WordTrace (prefixWord ++ tailWord_7104256) baseStart_7104256 baseEnd_7104256 := by
    simpa [prefixWord, tailWord_7104256, baseEnd_7104256] using wordTrace_append hprefix tailTrace_7104256
  have hstable : (prefixWord ++ tailWord_7104256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7104256).length < 2 ^ (prefixWord ++ tailWord_7104256).sum := by decide
  have hdescent : baseEnd_7104256 < baseStart_7104256 := by decide
  rcases family_descends (prefixWord ++ tailWord_7104256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7104274 : List Nat := [3, 2, 4, 1, 1, 1, 1, 4, 1, 3, 2]
def baseStart_7104274 : Nat := 118140960795 + 7104274 * 2 ^ 59
def prefixEnd_7104274 : Nat := 4983230072969 + 3 ^ 40 * 7104274 * 2
def baseEnd_7104274 : Nat := 3647907263239642729003045

theorem tailTrace_7104274 : CollatzResearch.WordTrace tailWord_7104274 prefixEnd_7104274 3647907263239642729003045 := by
  unfold tailWord_7104274
  simp only [CollatzResearch.WordTrace]
  refine ⟨64778539966109021561873969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172742773242957390831663917 64778539966109021561873969)
  ·
    refine ⟨48583904974581766171405477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64778539966109021561873969 48583904974581766171405477)
    ·
      refine ⟨9109482182734081157138527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48583904974581766171405477 9109482182734081157138527)
      ·
        refine ⟨13664223274101121735707791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9109482182734081157138527 13664223274101121735707791)
        ·
          refine ⟨20496334911151682603561687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13664223274101121735707791 20496334911151682603561687)
          ·
            refine ⟨30744502366727523905342531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20496334911151682603561687 30744502366727523905342531)
            ·
              refine ⟨46116753550091285858013797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30744502366727523905342531 46116753550091285858013797)
              ·
                refine ⟨8646891290642116098377587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46116753550091285858013797 8646891290642116098377587)
                ·
                  refine ⟨12970336935963174147566381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8646891290642116098377587 12970336935963174147566381)
                  ·
                    refine ⟨4863876350986190305337393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12970336935963174147566381 4863876350986190305337393)
                    ·
                      refine ⟨3647907263239642729003045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4863876350986190305337393 3647907263239642729003045)
                      ·
                        rfl

theorem cell23_7104274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_7104274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7104274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7104274 prefixEnd_7104274 := by exact prefixLift 7104274
  have htrace : WordTrace (prefixWord ++ tailWord_7104274) baseStart_7104274 baseEnd_7104274 := by
    simpa [prefixWord, tailWord_7104274, baseEnd_7104274] using wordTrace_append hprefix tailTrace_7104274
  have hstable : (prefixWord ++ tailWord_7104274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7104274).length < 2 ^ (prefixWord ++ tailWord_7104274).sum := by decide
  have hdescent : baseEnd_7104274 < baseStart_7104274 := by decide
  rcases family_descends (prefixWord ++ tailWord_7104274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7104340 : List Nat := [2, 4, 1, 1, 3, 1, 1, 3, 2, 5]
def baseStart_7104340 : Nat := 118140960795 + 7104340 * 2 ^ 59
def prefixEnd_7104340 : Nat := 4983230072969 + 3 ^ 40 * 7104340 * 2
def baseEnd_7104340 : Nat := 1215980384320946490259247

theorem tailTrace_7104340 : CollatzResearch.WordTrace tailWord_7104340 prefixEnd_7104340 1215980384320946490259247 := by
  unfold tailWord_7104340
  simp only [CollatzResearch.WordTrace]
  refine ⟨129558283541098489759699237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172744378054797986346265649 129558283541098489759699237)
  ·
    refine ⟨24292178163955966829943607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129558283541098489759699237 24292178163955966829943607)
    ·
      refine ⟨36438267245933950244915411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24292178163955966829943607 36438267245933950244915411)
      ·
        refine ⟨54657400868900925367373117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36438267245933950244915411 54657400868900925367373117)
        ·
          refine ⟨20496525325837847012764919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54657400868900925367373117 20496525325837847012764919)
          ·
            refine ⟨30744787988756770519147379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20496525325837847012764919 30744787988756770519147379)
            ·
              refine ⟨46117181983135155778721069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30744787988756770519147379 46117181983135155778721069)
              ·
                refine ⟨17293943243675683417020401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46117181983135155778721069 17293943243675683417020401)
                ·
                  refine ⟨12970457432756762562765301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17293943243675683417020401 12970457432756762562765301)
                  ·
                    refine ⟨1215980384320946490259247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12970457432756762562765301 1215980384320946490259247)
                    ·
                      rfl

theorem cell23_7104340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_7104340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7104340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7104340 prefixEnd_7104340 := by exact prefixLift 7104340
  have htrace : WordTrace (prefixWord ++ tailWord_7104340) baseStart_7104340 baseEnd_7104340 := by
    simpa [prefixWord, tailWord_7104340, baseEnd_7104340] using wordTrace_append hprefix tailTrace_7104340
  have hstable : (prefixWord ++ tailWord_7104340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7104340).length < 2 ^ (prefixWord ++ tailWord_7104340).sum := by decide
  have hdescent : baseEnd_7104340 < baseStart_7104340 := by decide
  rcases family_descends (prefixWord ++ tailWord_7104340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7104360 : List Nat := [2, 1, 4, 2, 1, 1, 1, 4, 2, 1, 4]
def baseStart_7104360 : Nat := 118140960795 + 7104360 * 2 ^ 59
def prefixEnd_7104360 : Nat := 4983230072969 + 3 ^ 40 * 7104360 * 2
def baseEnd_7104360 : Nat := 3647951422575929392527649

theorem tailTrace_7104360 : CollatzResearch.WordTrace tailWord_7104360 prefixEnd_7104360 3647951422575929392527649 := by
  unfold tailWord_7104360
  simp only [CollatzResearch.WordTrace]
  refine ⟨129558648271062261467563267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172744864361416348623417689 129558648271062261467563267)
  ·
    refine ⟨194337972406593392201344901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129558648271062261467563267 194337972406593392201344901)
    ·
      refine ⟨36438369826236261037752169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 194337972406593392201344901 36438369826236261037752169)
      ·
        refine ⟨27328777369677195778314127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36438369826236261037752169 27328777369677195778314127)
        ·
          refine ⟨40993166054515793667471191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27328777369677195778314127 40993166054515793667471191)
          ·
            refine ⟨61489749081773690501206787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40993166054515793667471191 61489749081773690501206787)
            ·
              refine ⟨92234623622660535751810181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61489749081773690501206787 92234623622660535751810181)
              ·
                refine ⟨17293991929248850453464409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92234623622660535751810181 17293991929248850453464409)
                ·
                  refine ⟨12970493946936637840098307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17293991929248850453464409 12970493946936637840098307)
                  ·
                    refine ⟨19455740920404956760147461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12970493946936637840098307 19455740920404956760147461)
                    ·
                      refine ⟨3647951422575929392527649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19455740920404956760147461 3647951422575929392527649)
                      ·
                        rfl

theorem cell23_7104360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_7104360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7104360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7104360 prefixEnd_7104360 := by exact prefixLift 7104360
  have htrace : WordTrace (prefixWord ++ tailWord_7104360) baseStart_7104360 baseEnd_7104360 := by
    simpa [prefixWord, tailWord_7104360, baseEnd_7104360] using wordTrace_append hprefix tailTrace_7104360
  have hstable : (prefixWord ++ tailWord_7104360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7104360).length < 2 ^ (prefixWord ++ tailWord_7104360).sum := by decide
  have hdescent : baseEnd_7104360 < baseStart_7104360 := by decide
  rcases family_descends (prefixWord ++ tailWord_7104360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7104363 : List Nat := [1, 1, 1, 1, 2, 2, 3, 2, 3, 4, 3]
def baseStart_7104363 : Nat := 118140960795 + 7104363 * 2 ^ 59
def prefixEnd_7104363 : Nat := 4983230072969 + 3 ^ 40 * 7104363 * 2
def baseEnd_7104363 : Nat := 3647952963017892880790135

theorem tailTrace_7104363 : CollatzResearch.WordTrace tailWord_7104363 prefixEnd_7104363 3647952963017892880790135 := by
  unfold tailWord_7104363
  simp only [CollatzResearch.WordTrace]
  refine ⟨259117405961113654447485743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172744937307409102964990495 259117405961113654447485743)
  ·
    refine ⟨388676108941670481671228615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259117405961113654447485743 388676108941670481671228615)
    ·
      refine ⟨583014163412505722506842923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388676108941670481671228615 583014163412505722506842923)
      ·
        refine ⟨874521245118758583760264385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 583014163412505722506842923 874521245118758583760264385)
        ·
          refine ⟨655890933839068937820198289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 874521245118758583760264385 655890933839068937820198289)
          ·
            refine ⟨491918200379301703365148717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 655890933839068937820198289 491918200379301703365148717)
            ·
              refine ⟨184469325142238138761930769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 491918200379301703365148717 184469325142238138761930769)
              ·
                refine ⟨138351993856678604071448077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184469325142238138761930769 138351993856678604071448077)
                ·
                  refine ⟨51881997696254476526793029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 138351993856678604071448077 51881997696254476526793029)
                  ·
                    refine ⟨9727874568047714348773693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51881997696254476526793029 9727874568047714348773693)
                    ·
                      refine ⟨3647952963017892880790135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9727874568047714348773693 3647952963017892880790135)
                      ·
                        rfl

theorem cell23_7104363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 4, 3].length) (baseStart_7104363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7104363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7104363 prefixEnd_7104363 := by exact prefixLift 7104363
  have htrace : WordTrace (prefixWord ++ tailWord_7104363) baseStart_7104363 baseEnd_7104363 := by
    simpa [prefixWord, tailWord_7104363, baseEnd_7104363] using wordTrace_append hprefix tailTrace_7104363
  have hstable : (prefixWord ++ tailWord_7104363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7104363).length < 2 ^ (prefixWord ++ tailWord_7104363).sum := by decide
  have hdescent : baseEnd_7104363 < baseStart_7104363 := by decide
  rcases family_descends (prefixWord ++ tailWord_7104363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7104370 : List Nat := [3, 2, 1, 2, 1, 1, 1, 5, 3, 4]
def baseStart_7104370 : Nat := 118140960795 + 7104370 * 2 ^ 59
def prefixEnd_7104370 : Nat := 4983230072969 + 3 ^ 40 * 7104370 * 2
def baseEnd_7104370 : Nat := 1215985519127491451134201

theorem tailTrace_7104370 : CollatzResearch.WordTrace tailWord_7104370 prefixEnd_7104370 1215985519127491451134201 := by
  unfold tailWord_7104370
  simp only [CollatzResearch.WordTrace]
  refine ⟨64779415318022073660747641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172745107514725529761993709 64779415318022073660747641)
  ·
    refine ⟨48584561488516555245560731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64779415318022073660747641 48584561488516555245560731)
    ·
      refine ⟨72876842232774832868341097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48584561488516555245560731 72876842232774832868341097)
      ·
        refine ⟨54657631674581124651255823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72876842232774832868341097 54657631674581124651255823)
        ·
          refine ⟨81986447511871686976883735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54657631674581124651255823 81986447511871686976883735)
          ·
            refine ⟨122979671267807530465325603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81986447511871686976883735 122979671267807530465325603)
            ·
              refine ⟨184469506901711295697988405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122979671267807530465325603 184469506901711295697988405)
              ·
                refine ⟨17294016272035433971686413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 184469506901711295697988405 17294016272035433971686413)
                ·
                  refine ⟨6485256102013287739382405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17294016272035433971686413 6485256102013287739382405)
                  ·
                    refine ⟨1215985519127491451134201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6485256102013287739382405 1215985519127491451134201)
                    ·
                      rfl

theorem cell23_7104370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 5, 3, 4].length) (baseStart_7104370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7104370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7104370 prefixEnd_7104370 := by exact prefixLift 7104370
  have htrace : WordTrace (prefixWord ++ tailWord_7104370) baseStart_7104370 baseEnd_7104370 := by
    simpa [prefixWord, tailWord_7104370, baseEnd_7104370] using wordTrace_append hprefix tailTrace_7104370
  have hstable : (prefixWord ++ tailWord_7104370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7104370).length < 2 ^ (prefixWord ++ tailWord_7104370).sum := by decide
  have hdescent : baseEnd_7104370 < baseStart_7104370 := by decide
  rcases family_descends (prefixWord ++ tailWord_7104370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7104394 : List Nat := [3, 1, 2, 4, 2, 2, 1, 1, 2, 1, 4]
def baseStart_7104394 : Nat := 118140960795 + 7104394 * 2 ^ 59
def prefixEnd_7104394 : Nat := 4983230072969 + 3 ^ 40 * 7104394 * 2
def baseEnd_7104394 : Nat := 3647968880918182259502493

theorem tailTrace_7104394 : CollatzResearch.WordTrace tailWord_7104394 prefixEnd_7104394 3647968880918182259502493 := by
  unfold tailWord_7104394
  simp only [CollatzResearch.WordTrace]
  refine ⟨64779634156000336685466059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172745691082667564494576157 64779634156000336685466059)
  ·
    refine ⟨97169451234000505028199089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64779634156000336685466059 97169451234000505028199089)
    ·
      refine ⟨72877088425500378771149317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97169451234000505028199089 72877088425500378771149317)
      ·
        refine ⟨13664454079781321019590497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72877088425500378771149317 13664454079781321019590497)
        ·
          refine ⟨10248340559835990764692873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13664454079781321019590497 10248340559835990764692873)
          ·
            refine ⟨7686255419876993073519655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10248340559835990764692873 7686255419876993073519655)
            ·
              refine ⟨11529383129815489610279483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7686255419876993073519655 11529383129815489610279483)
              ·
                refine ⟨17294074694723234415419225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11529383129815489610279483 17294074694723234415419225)
                ·
                  refine ⟨12970556021042425811564419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17294074694723234415419225 12970556021042425811564419)
                  ·
                    refine ⟨19455834031563638717346629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12970556021042425811564419 19455834031563638717346629)
                    ·
                      refine ⟨3647968880918182259502493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19455834031563638717346629 3647968880918182259502493)
                      ·
                        rfl

theorem cell23_7104394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_7104394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7104394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7104394 prefixEnd_7104394 := by exact prefixLift 7104394
  have htrace : WordTrace (prefixWord ++ tailWord_7104394) baseStart_7104394 baseEnd_7104394 := by
    simpa [prefixWord, tailWord_7104394, baseEnd_7104394] using wordTrace_append hprefix tailTrace_7104394
  have hstable : (prefixWord ++ tailWord_7104394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7104394).length < 2 ^ (prefixWord ++ tailWord_7104394).sum := by decide
  have hdescent : baseEnd_7104394 < baseStart_7104394 := by decide
  rcases family_descends (prefixWord ++ tailWord_7104394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7104404 : List Nat := [2, 4, 2, 1, 1, 2, 1, 5, 1, 4]
def baseStart_7104404 : Nat := 118140960795 + 7104404 * 2 ^ 59
def prefixEnd_7104404 : Nat := 4983230072969 + 3 ^ 40 * 7104404 * 2
def baseEnd_7104404 : Nat := 1215991338574909073459149

theorem tailTrace_7104404 : CollatzResearch.WordTrace tailWord_7104404 prefixEnd_7104404 1215991338574909073459149 := by
  unfold tailWord_7104404
  simp only [CollatzResearch.WordTrace]
  refine ⟨129559450676982559224864133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172745934235976745633152177 129559450676982559224864133)
  ·
    refine ⟨24292397001934229854662025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129559450676982559224864133 24292397001934229854662025)
    ·
      refine ⟨18219297751450672390996519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24292397001934229854662025 18219297751450672390996519)
      ·
        refine ⟨27328946627176008586494779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18219297751450672390996519 27328946627176008586494779)
        ·
          refine ⟨40993419940764012879742169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27328946627176008586494779 40993419940764012879742169)
          ·
            refine ⟨30745064955573009659806627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40993419940764012879742169 30745064955573009659806627)
            ·
              refine ⟨46117597433359514489709941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30745064955573009659806627 46117597433359514489709941)
              ·
                refine ⟨4323524759377454483410307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46117597433359514489709941 4323524759377454483410307)
                ·
                  refine ⟨6485287139066181725115461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4323524759377454483410307 6485287139066181725115461)
                  ·
                    refine ⟨1215991338574909073459149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6485287139066181725115461 1215991338574909073459149)
                    ·
                      rfl

theorem cell23_7104404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_7104404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7104404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7104404 prefixEnd_7104404 := by exact prefixLift 7104404
  have htrace : WordTrace (prefixWord ++ tailWord_7104404) baseStart_7104404 baseEnd_7104404 := by
    simpa [prefixWord, tailWord_7104404, baseEnd_7104404] using wordTrace_append hprefix tailTrace_7104404
  have hstable : (prefixWord ++ tailWord_7104404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7104404).length < 2 ^ (prefixWord ++ tailWord_7104404).sum := by decide
  have hdescent : baseEnd_7104404 < baseStart_7104404 := by decide
  rcases family_descends (prefixWord ++ tailWord_7104404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7104437 : List Nat := [1, 3, 3, 2, 1, 2, 1, 2, 1, 5, 2]
def baseStart_7104437 : Nat := 118140960795 + 7104437 * 2 ^ 59
def prefixEnd_7104437 : Nat := 4983230072969 + 3 ^ 40 * 7104437 * 2
def baseEnd_7104437 : Nat := 3647990960586325591264795

theorem tailTrace_7104437 : CollatzResearch.WordTrace tailWord_7104437 prefixEnd_7104437 3647990960586325591264795 := by
  unfold tailWord_7104437
  simp only [CollatzResearch.WordTrace]
  refine ⟨259120104962845565085679565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172746736641897043390453043 259120104962845565085679565)
  ·
    refine ⟨97170039361067086907129837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259120104962845565085679565 97170039361067086907129837)
    ·
      refine ⟨36438764760400157590173689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97170039361067086907129837 36438764760400157590173689)
      ·
        refine ⟨27329073570300118192630267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36438764760400157590173689 27329073570300118192630267)
        ·
          refine ⟨40993610355450177288945401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27329073570300118192630267 40993610355450177288945401)
          ·
            refine ⟨30745207766587632966709051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40993610355450177288945401 30745207766587632966709051)
            ·
              refine ⟨46117811649881449450063577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30745207766587632966709051 46117811649881449450063577)
              ·
                refine ⟨34588358737411087087547683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46117811649881449450063577 34588358737411087087547683)
                ·
                  refine ⟨51882538106116630631321525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34588358737411087087547683 51882538106116630631321525)
                  ·
                    refine ⟨4863987947448434121686393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51882538106116630631321525 4863987947448434121686393)
                    ·
                      refine ⟨3647990960586325591264795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4863987947448434121686393 3647990960586325591264795)
                      ·
                        rfl

theorem cell23_7104437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 5, 2].length) (baseStart_7104437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7104437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7104437 prefixEnd_7104437 := by exact prefixLift 7104437
  have htrace : WordTrace (prefixWord ++ tailWord_7104437) baseStart_7104437 baseEnd_7104437 := by
    simpa [prefixWord, tailWord_7104437, baseEnd_7104437] using wordTrace_append hprefix tailTrace_7104437
  have hstable : (prefixWord ++ tailWord_7104437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7104437).length < 2 ^ (prefixWord ++ tailWord_7104437).sum := by decide
  have hdescent : baseEnd_7104437 < baseStart_7104437 := by decide
  rcases family_descends (prefixWord ++ tailWord_7104437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7104490 : List Nat := [3, 1, 3, 1, 2, 1, 4, 8]
def baseStart_7104490 : Nat := 118140960795 + 7104490 * 2 ^ 59
def prefixEnd_7104490 : Nat := 4983230072969 + 3 ^ 40 * 7104490 * 2
def baseEnd_7104490 : Nat := 135111784261519032737113

theorem tailTrace_7104490 : CollatzResearch.WordTrace tailWord_7104490 prefixEnd_7104490 135111784261519032737113 := by
  unfold tailWord_7104490
  simp only [CollatzResearch.WordTrace]
  refine ⟨64780509507913388784339731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172748025354435703424905949 64780509507913388784339731)
  ·
    refine ⟨97170764261870083176509597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64780509507913388784339731 97170764261870083176509597)
    ·
      refine ⟨36439036598201281191191099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97170764261870083176509597 36439036598201281191191099)
      ·
        refine ⟨54658554897301921786786649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36439036598201281191191099 54658554897301921786786649)
        ·
          refine ⟨40993916172976441340089987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54658554897301921786786649 40993916172976441340089987)
          ·
            refine ⟨61490874259464662010134981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40993916172976441340089987 61490874259464662010134981)
            ·
              refine ⟨11529538923649624126900309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61490874259464662010134981 11529538923649624126900309)
              ·
                refine ⟨135111784261519032737113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11529538923649624126900309 135111784261519032737113)
                ·
                  rfl

theorem cell23_7104490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 8].length) (baseStart_7104490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7104490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7104490 prefixEnd_7104490 := by exact prefixLift 7104490
  have htrace : WordTrace (prefixWord ++ tailWord_7104490) baseStart_7104490 baseEnd_7104490 := by
    simpa [prefixWord, tailWord_7104490, baseEnd_7104490] using wordTrace_append hprefix tailTrace_7104490
  have hstable : (prefixWord ++ tailWord_7104490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7104490).length < 2 ^ (prefixWord ++ tailWord_7104490).sum := by decide
  have hdescent : baseEnd_7104490 < baseStart_7104490 := by decide
  rcases family_descends (prefixWord ++ tailWord_7104490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7104494 : List Nat := [4, 1, 2, 1, 3, 2, 1, 3, 2, 4]
def baseStart_7104494 : Nat := 118140960795 + 7104494 * 2 ^ 59
def prefixEnd_7104494 : Nat := 4983230072969 + 3 ^ 40 * 7104494 * 2
def baseEnd_7104494 : Nat := 1216006742994543956084011

theorem tailTrace_7104494 : CollatzResearch.WordTrace tailWord_7104494 prefixEnd_7104494 1216006742994543956084011 := by
  unfold tailWord_7104494
  simp only [CollatzResearch.WordTrace]
  refine ⟨32390272990454882977563067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172748122615759375880336357 32390272990454882977563067)
  ·
    refine ⟨48585409485682324466344601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32390272990454882977563067 48585409485682324466344601)
    ·
      refine ⟨36439057114261743349758451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48585409485682324466344601 36439057114261743349758451)
      ·
        refine ⟨54658585671392615024637677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36439057114261743349758451 54658585671392615024637677)
        ·
          refine ⟨20496969626772230634239129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54658585671392615024637677 20496969626772230634239129)
          ·
            refine ⟨15372727220079172975679347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20496969626772230634239129 15372727220079172975679347)
            ·
              refine ⟨23059090830118759463519021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15372727220079172975679347 23059090830118759463519021)
              ·
                refine ⟨8647159061294534798819633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23059090830118759463519021 8647159061294534798819633)
                ·
                  refine ⟨6485369295970901099114725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8647159061294534798819633 6485369295970901099114725)
                  ·
                    refine ⟨1216006742994543956084011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6485369295970901099114725 1216006742994543956084011)
                    ·
                      rfl

theorem cell23_7104494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 3, 2, 4].length) (baseStart_7104494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7104494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7104494 prefixEnd_7104494 := by exact prefixLift 7104494
  have htrace : WordTrace (prefixWord ++ tailWord_7104494) baseStart_7104494 baseEnd_7104494 := by
    simpa [prefixWord, tailWord_7104494, baseEnd_7104494] using wordTrace_append hprefix tailTrace_7104494
  have hstable : (prefixWord ++ tailWord_7104494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7104494).length < 2 ^ (prefixWord ++ tailWord_7104494).sum := by decide
  have hdescent : baseEnd_7104494 < baseStart_7104494 := by decide
  rcases family_descends (prefixWord ++ tailWord_7104494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7104517 : List Nat := [1, 3, 1, 1, 2, 5, 1, 2, 1, 3, 3]
def baseStart_7104517 : Nat := 118140960795 + 7104517 * 2 ^ 59
def prefixEnd_7104517 : Nat := 4983230072969 + 3 ^ 40 * 7104517 * 2
def baseEnd_7104517 : Nat := 3648032039038685278264427

theorem tailTrace_7104517 : CollatzResearch.WordTrace tailWord_7104517 prefixEnd_7104517 3648032039038685278264427 := by
  unfold tailWord_7104517
  simp only [CollatzResearch.WordTrace]
  refine ⟨259123022802555738748591805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172748681868370492499061203 259123022802555738748591805)
  ·
    refine ⟨97171133550958402030721927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259123022802555738748591805 97171133550958402030721927)
    ·
      refine ⟨145756700326437603046082891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97171133550958402030721927 145756700326437603046082891)
      ·
        refine ⟨218635050489656404569124337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145756700326437603046082891 218635050489656404569124337)
        ·
          refine ⟨163976287867242303426843253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218635050489656404569124337 163976287867242303426843253)
          ·
            refine ⟨15372776987553965946266555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 163976287867242303426843253 15372776987553965946266555)
            ·
              refine ⟨23059165481330948919399833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15372776987553965946266555 23059165481330948919399833)
              ·
                refine ⟨17294374110998211689549875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23059165481330948919399833 17294374110998211689549875)
                ·
                  refine ⟨25941561166497317534324813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17294374110998211689549875 25941561166497317534324813)
                  ·
                    refine ⟨9728085437436494075371805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25941561166497317534324813 9728085437436494075371805)
                    ·
                      refine ⟨3648032039038685278264427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9728085437436494075371805 3648032039038685278264427)
                      ·
                        rfl

theorem cell23_7104517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 2, 1, 3, 3].length) (baseStart_7104517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7104517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7104517 prefixEnd_7104517 := by exact prefixLift 7104517
  have htrace : WordTrace (prefixWord ++ tailWord_7104517) baseStart_7104517 baseEnd_7104517 := by
    simpa [prefixWord, tailWord_7104517, baseEnd_7104517] using wordTrace_append hprefix tailTrace_7104517
  have hstable : (prefixWord ++ tailWord_7104517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7104517).length < 2 ^ (prefixWord ++ tailWord_7104517).sum := by decide
  have hdescent : baseEnd_7104517 < baseStart_7104517 := by decide
  rcases family_descends (prefixWord ++ tailWord_7104517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7104551 : List Nat := [1, 1, 7, 1, 2, 1, 2, 1, 1, 3, 3]
def baseStart_7104551 : Nat := 118140960795 + 7104551 * 2 ^ 59
def prefixEnd_7104551 : Nat := 4983230072969 + 3 ^ 40 * 7104551 * 2
def baseEnd_7104551 : Nat := 3648049497380938145239271

theorem tailTrace_7104551 : CollatzResearch.WordTrace tailWord_7104551 prefixEnd_7104551 3648049497380938145239271 := by
  unfold tailWord_7104551
  simp only [CollatzResearch.WordTrace]
  refine ⟨259124262884432562555329507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172749508589621708370219671 259124262884432562555329507)
  ·
    refine ⟨388686394326648843832994261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259124262884432562555329507 388686394326648843832994261)
    ·
      refine ⟨9109837367030832277335803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 388686394326648843832994261 9109837367030832277335803)
      ·
        refine ⟨13664756050546248416003705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9109837367030832277335803 13664756050546248416003705)
        ·
          refine ⟨10248567037909686312002779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13664756050546248416003705 10248567037909686312002779)
          ·
            refine ⟨15372850556864529468004169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10248567037909686312002779 15372850556864529468004169)
            ·
              refine ⟨11529637917648397101003127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15372850556864529468004169 11529637917648397101003127)
              ·
                refine ⟨17294456876472595651504691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11529637917648397101003127 17294456876472595651504691)
                ·
                  refine ⟨25941685314708893477257037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17294456876472595651504691 25941685314708893477257037)
                  ·
                    refine ⟨9728131993015835053971389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25941685314708893477257037 9728131993015835053971389)
                    ·
                      refine ⟨3648049497380938145239271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9728131993015835053971389 3648049497380938145239271)
                      ·
                        rfl

theorem cell23_7104551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_7104551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7104551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7104551 prefixEnd_7104551 := by exact prefixLift 7104551
  have htrace : WordTrace (prefixWord ++ tailWord_7104551) baseStart_7104551 baseEnd_7104551 := by
    simpa [prefixWord, tailWord_7104551, baseEnd_7104551] using wordTrace_append hprefix tailTrace_7104551
  have hstable : (prefixWord ++ tailWord_7104551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7104551).length < 2 ^ (prefixWord ++ tailWord_7104551).sum := by decide
  have hdescent : baseEnd_7104551 < baseStart_7104551 := by decide
  rcases family_descends (prefixWord ++ tailWord_7104551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7104570 : List Nat := [3, 1, 1, 1, 3, 1, 1, 1, 3, 4, 4]
def baseStart_7104570 : Nat := 118140960795 + 7104570 * 2 ^ 59
def prefixEnd_7104570 : Nat := 4983230072969 + 3 ^ 40 * 7104570 * 2
def baseEnd_7104570 : Nat := 3648059253513373570901683

theorem tailTrace_7104570 : CollatzResearch.WordTrace tailWord_7104570 prefixEnd_7104570 3648059253513373570901683 := by
  unfold tailWord_7104570
  simp only [CollatzResearch.WordTrace]
  refine ⟨64781238967840932200067791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172749970580909152533514109 64781238967840932200067791)
  ·
    refine ⟨97171858451761398300101687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64781238967840932200067791 97171858451761398300101687)
    ·
      refine ⟨145757787677642097450152531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97171858451761398300101687 145757787677642097450152531)
      ·
        refine ⟨218636681516463146175228797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145757787677642097450152531 218636681516463146175228797)
        ·
          refine ⟨81988755568673679815710799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218636681516463146175228797 81988755568673679815710799)
          ·
            refine ⟨122983133353010519723566199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81988755568673679815710799 122983133353010519723566199)
            ·
              refine ⟨184474700029515779585349299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122983133353010519723566199 184474700029515779585349299)
              ·
                refine ⟨276712050044273669378023949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184474700029515779585349299 276712050044273669378023949)
                ·
                  refine ⟨103767018766602626016758981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 276712050044273669378023949 103767018766602626016758981)
                  ·
                    refine ⟨19456316018737992378142309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 103767018766602626016758981 19456316018737992378142309)
                    ·
                      refine ⟨3648059253513373570901683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19456316018737992378142309 3648059253513373570901683)
                      ·
                        rfl

theorem cell23_7104570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 3, 4, 4].length) (baseStart_7104570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7104570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7104570 prefixEnd_7104570 := by exact prefixLift 7104570
  have htrace : WordTrace (prefixWord ++ tailWord_7104570) baseStart_7104570 baseEnd_7104570 := by
    simpa [prefixWord, tailWord_7104570, baseEnd_7104570] using wordTrace_append hprefix tailTrace_7104570
  have hstable : (prefixWord ++ tailWord_7104570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7104570).length < 2 ^ (prefixWord ++ tailWord_7104570).sum := by decide
  have hdescent : baseEnd_7104570 < baseStart_7104570 := by decide
  rcases family_descends (prefixWord ++ tailWord_7104570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7104597 : List Nat := [1, 3, 2, 2, 1, 4, 2, 1, 7]
def baseStart_7104597 : Nat := 118140960795 + 7104597 * 2 ^ 59
def prefixEnd_7104597 : Nat := 4983230072969 + 3 ^ 40 * 7104597 * 2
def baseEnd_7104597 : Nat := 405341457499004996140451

theorem tailTrace_7104597 : CollatzResearch.WordTrace tailWord_7104597 prefixEnd_7104597 405341457499004996140451 := by
  unfold tailWord_7104597
  simp only [CollatzResearch.WordTrace]
  refine ⟨259125940642265912411504045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172750627094843941607669363 259125940642265912411504045)
  ·
    refine ⟨97172227740849717154314017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259125940642265912411504045 97172227740849717154314017)
    ·
      refine ⟨72879170805637287865735513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97172227740849717154314017 72879170805637287865735513)
      ·
        refine ⟨54659378104227965899301635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72879170805637287865735513 54659378104227965899301635)
        ·
          refine ⟨81989067156341948848952453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54659378104227965899301635 81989067156341948848952453)
          ·
            refine ⟨15372950091814115409178585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81989067156341948848952453 15372950091814115409178585)
            ·
              refine ⟨11529712568860586556883939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15372950091814115409178585 11529712568860586556883939)
              ·
                refine ⟨17294568853290879835325909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11529712568860586556883939 17294568853290879835325909)
                ·
                  refine ⟨405341457499004996140451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17294568853290879835325909 405341457499004996140451)
                  ·
                    rfl

theorem cell23_7104597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 1, 7].length) (baseStart_7104597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7104597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7104597 prefixEnd_7104597 := by exact prefixLift 7104597
  have htrace : WordTrace (prefixWord ++ tailWord_7104597) baseStart_7104597 baseEnd_7104597 := by
    simpa [prefixWord, tailWord_7104597, baseEnd_7104597] using wordTrace_append hprefix tailTrace_7104597
  have hstable : (prefixWord ++ tailWord_7104597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7104597).length < 2 ^ (prefixWord ++ tailWord_7104597).sum := by decide
  have hdescent : baseEnd_7104597 < baseStart_7104597 := by decide
  rcases family_descends (prefixWord ++ tailWord_7104597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7104608 : List Nat := [2, 1, 1, 3, 2, 4, 3, 1, 2, 2, 2]
def baseStart_7104608 : Nat := 118140960795 + 7104608 * 2 ^ 59
def prefixEnd_7104608 : Nat := 4983230072969 + 3 ^ 40 * 7104608 * 2
def baseEnd_7104608 : Nat := 3648078765778244422226509

theorem tailTrace_7104608 : CollatzResearch.WordTrace tailWord_7104608 prefixEnd_7104608 3648078765778244422226509 := by
  unfold tailWord_7104608
  simp only [CollatzResearch.WordTrace]
  refine ⟨129563170922613030645077239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172750894563484040860102985 129563170922613030645077239)
  ·
    refine ⟨194344756383919545967615859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129563170922613030645077239 194344756383919545967615859)
    ·
      refine ⟨291517134575879318951423789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194344756383919545967615859 291517134575879318951423789)
      ·
        refine ⟨109318925465954744606783921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 291517134575879318951423789 109318925465954744606783921)
        ·
          refine ⟨81989194099466058455087941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109318925465954744606783921 81989194099466058455087941)
          ·
            refine ⟨15372973893649885960328989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81989194099466058455087941 15372973893649885960328989)
            ·
              refine ⟨5764865210118707235123371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15372973893649885960328989 5764865210118707235123371)
              ·
                refine ⟨8647297815178060852685057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5764865210118707235123371 8647297815178060852685057)
                ·
                  refine ⟨6485473361383545639513793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8647297815178060852685057 6485473361383545639513793)
                  ·
                    refine ⟨4864105021037659229635345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6485473361383545639513793 4864105021037659229635345)
                    ·
                      refine ⟨3648078765778244422226509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4864105021037659229635345 3648078765778244422226509)
                      ·
                        rfl

theorem cell23_7104608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 3, 1, 2, 2, 2].length) (baseStart_7104608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7104608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7104608 prefixEnd_7104608 := by exact prefixLift 7104608
  have htrace : WordTrace (prefixWord ++ tailWord_7104608) baseStart_7104608 baseEnd_7104608 := by
    simpa [prefixWord, tailWord_7104608, baseEnd_7104608] using wordTrace_append hprefix tailTrace_7104608
  have hstable : (prefixWord ++ tailWord_7104608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7104608).length < 2 ^ (prefixWord ++ tailWord_7104608).sum := by decide
  have hdescent : baseEnd_7104608 < baseStart_7104608 := by decide
  rcases family_descends (prefixWord ++ tailWord_7104608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7104647 : List Nat := [1, 1, 4, 2, 1, 1, 3, 1, 4, 1, 4]
def baseStart_7104647 : Nat := 118140960795 + 7104647 * 2 ^ 59
def prefixEnd_7104647 : Nat := 4983230072969 + 3 ^ 40 * 7104647 * 2
def baseEnd_7104647 : Nat := 3648098791523769769638829

theorem tailTrace_7104647 : CollatzResearch.WordTrace tailWord_7104647 prefixEnd_7104647 3648098791523769769638829 := by
  unfold tailWord_7104647
  simp only [CollatzResearch.WordTrace]
  refine ⟨259127764292084770950824195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172751842861389847300549463 259127764292084770950824195)
  ·
    refine ⟨388691646438127156426236293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259127764292084770950824195 388691646438127156426236293)
    ·
      refine ⟨72879683707148841829919305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 388691646438127156426236293 72879683707148841829919305)
      ·
        refine ⟨54659762780361631372439479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72879683707148841829919305 54659762780361631372439479)
        ·
          refine ⟨81989644170542447058659219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54659762780361631372439479 81989644170542447058659219)
          ·
            refine ⟨122984466255813670587988829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81989644170542447058659219 122984466255813670587988829)
            ·
              refine ⟨46119174845930126470495811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122984466255813670587988829 46119174845930126470495811)
              ·
                refine ⟨69178762268895189705743717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46119174845930126470495811 69178762268895189705743717)
                ·
                  refine ⟨12971017925417848069826947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69178762268895189705743717 12971017925417848069826947)
                  ·
                    refine ⟨19456526888126772104740421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12971017925417848069826947 19456526888126772104740421)
                    ·
                      refine ⟨3648098791523769769638829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19456526888126772104740421 3648098791523769769638829)
                      ·
                        rfl

theorem cell23_7104647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_7104647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7104647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7104647 prefixEnd_7104647 := by exact prefixLift 7104647
  have htrace : WordTrace (prefixWord ++ tailWord_7104647) baseStart_7104647 baseEnd_7104647 := by
    simpa [prefixWord, tailWord_7104647, baseEnd_7104647] using wordTrace_append hprefix tailTrace_7104647
  have hstable : (prefixWord ++ tailWord_7104647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7104647).length < 2 ^ (prefixWord ++ tailWord_7104647).sum := by decide
  have hdescent : baseEnd_7104647 < baseStart_7104647 := by decide
  rcases family_descends (prefixWord ++ tailWord_7104647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7104654 : List Nat := [4, 1, 1, 3, 3, 1, 1, 1, 1, 2, 5]
def baseStart_7104654 : Nat := 118140960795 + 7104654 * 2 ^ 59
def prefixEnd_7104654 : Nat := 4983230072969 + 3 ^ 40 * 7104654 * 2
def baseEnd_7104654 : Nat := 3648102385888351242251297

theorem tailTrace_7104654 : CollatzResearch.WordTrace tailWord_7104654 prefixEnd_7104654 3648102385888351242251297 := by
  unfold tailWord_7104654
  simp only [CollatzResearch.WordTrace]
  refine ⟨32391002450382426393291127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172752013068706274097552677 32391002450382426393291127)
  ·
    refine ⟨48586503675573639589936691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32391002450382426393291127 48586503675573639589936691)
    ·
      refine ⟨72879755513360459384905037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48586503675573639589936691 72879755513360459384905037)
      ·
        refine ⟨27329908317510172269339389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72879755513360459384905037 27329908317510172269339389)
        ·
          refine ⟨10248715619066314601002271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27329908317510172269339389 10248715619066314601002271)
          ·
            refine ⟨15373073428599471901503407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10248715619066314601002271 15373073428599471901503407)
            ·
              refine ⟨23059610142899207852255111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15373073428599471901503407 23059610142899207852255111)
              ·
                refine ⟨34589415214348811778382667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23059610142899207852255111 34589415214348811778382667)
                ·
                  refine ⟨51884122821523217667574001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34589415214348811778382667 51884122821523217667574001)
                  ·
                    refine ⟨38913092116142413250680501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51884122821523217667574001 38913092116142413250680501)
                    ·
                      refine ⟨3648102385888351242251297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38913092116142413250680501 3648102385888351242251297)
                      ·
                        rfl

theorem cell23_7104654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_7104654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7104654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7104654 prefixEnd_7104654 := by exact prefixLift 7104654
  have htrace : WordTrace (prefixWord ++ tailWord_7104654) baseStart_7104654 baseEnd_7104654 := by
    simpa [prefixWord, tailWord_7104654, baseEnd_7104654] using wordTrace_append hprefix tailTrace_7104654
  have hstable : (prefixWord ++ tailWord_7104654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7104654).length < 2 ^ (prefixWord ++ tailWord_7104654).sum := by decide
  have hdescent : baseEnd_7104654 < baseStart_7104654 := by decide
  rcases family_descends (prefixWord ++ tailWord_7104654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7104667 : List Nat := [1, 1, 1, 1, 1, 1, 2, 6, 4, 2, 3]
def baseStart_7104667 : Nat := 118140960795 + 7104667 * 2 ^ 59
def prefixEnd_7104667 : Nat := 4983230072969 + 3 ^ 40 * 7104667 * 2
def baseEnd_7104667 : Nat := 3648109061136859691388737

theorem tailTrace_7104667 : CollatzResearch.WordTrace tailWord_7104667 prefixEnd_7104667 3648109061136859691388737 := by
  unfold tailWord_7104667
  simp only [CollatzResearch.WordTrace]
  refine ⟨259128493752012314366552255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172752329168008209577701503 259128493752012314366552255)
  ·
    refine ⟨388692740628018471549828383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259128493752012314366552255 388692740628018471549828383)
    ·
      refine ⟨583039110942027707324742575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388692740628018471549828383 583039110942027707324742575)
      ·
        refine ⟨874558666413041560987113863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 583039110942027707324742575 874558666413041560987113863)
        ·
          refine ⟨1311837999619562341480670795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 874558666413041560987113863 1311837999619562341480670795)
          ·
            refine ⟨1967756999429343512221006193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1311837999619562341480670795 1967756999429343512221006193)
            ·
              refine ⟨1475817749572007634165754645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1967756999429343512221006193 1475817749572007634165754645)
              ·
                refine ⟨69178957011187857851519749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1475817749572007634165754645 69178957011187857851519749)
                ·
                  refine ⟨12971054439597723347159953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69178957011187857851519749 12971054439597723347159953)
                  ·
                    refine ⟨9728290829698292510369965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12971054439597723347159953 9728290829698292510369965)
                    ·
                      refine ⟨3648109061136859691388737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9728290829698292510369965 3648109061136859691388737)
                      ·
                        rfl

theorem cell23_7104667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 4, 2, 3].length) (baseStart_7104667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7104667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7104667 prefixEnd_7104667 := by exact prefixLift 7104667
  have htrace : WordTrace (prefixWord ++ tailWord_7104667) baseStart_7104667 baseEnd_7104667 := by
    simpa [prefixWord, tailWord_7104667, baseEnd_7104667] using wordTrace_append hprefix tailTrace_7104667
  have hstable : (prefixWord ++ tailWord_7104667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7104667).length < 2 ^ (prefixWord ++ tailWord_7104667).sum := by decide
  have hdescent : baseEnd_7104667 < baseStart_7104667 := by decide
  rcases family_descends (prefixWord ++ tailWord_7104667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7104704 : List Nat := [2, 1, 1, 2, 5, 2, 2, 2, 6]
def baseStart_7104704 : Nat := 118140960795 + 7104704 * 2 ^ 59
def prefixEnd_7104704 : Nat := 4983230072969 + 3 ^ 40 * 7104704 * 2
def baseEnd_7104704 : Nat := 405347562213452894069563

theorem tailTrace_7104704 : CollatzResearch.WordTrace tailWord_7104704 prefixEnd_7104704 405347562213452894069563 := by
  unfold tailWord_7104704
  simp only [CollatzResearch.WordTrace]
  refine ⟨129564921626439134842824583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172753228835252179790432777 129564921626439134842824583)
  ·
    refine ⟨194347382439658702264236875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129564921626439134842824583 194347382439658702264236875)
    ·
      refine ⟨291521073659488053396355313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194347382439658702264236875 291521073659488053396355313)
      ·
        refine ⟨218640805244616040047266485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291521073659488053396355313 218640805244616040047266485)
        ·
          refine ⟨20497575491682753754431233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 218640805244616040047266485 20497575491682753754431233)
          ·
            refine ⟨15373181618762065315823425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20497575491682753754431233 15373181618762065315823425)
            ·
              refine ⟨11529886214071548986867569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15373181618762065315823425 11529886214071548986867569)
              ·
                refine ⟨8647414660553661740150677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11529886214071548986867569 8647414660553661740150677)
                ·
                  refine ⟨405347562213452894069563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8647414660553661740150677 405347562213452894069563)
                  ·
                    rfl

theorem cell23_7104704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 2, 6].length) (baseStart_7104704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7104704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7104704 prefixEnd_7104704 := by exact prefixLift 7104704
  have htrace : WordTrace (prefixWord ++ tailWord_7104704) baseStart_7104704 baseEnd_7104704 := by
    simpa [prefixWord, tailWord_7104704, baseEnd_7104704] using wordTrace_append hprefix tailTrace_7104704
  have hstable : (prefixWord ++ tailWord_7104704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7104704).length < 2 ^ (prefixWord ++ tailWord_7104704).sum := by decide
  have hdescent : baseEnd_7104704 < baseStart_7104704 := by decide
  rcases family_descends (prefixWord ++ tailWord_7104704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7104708 : List Nat := [2, 3, 3, 1, 2, 2, 1, 4, 1, 4]
def baseStart_7104708 : Nat := 118140960795 + 7104708 * 2 ^ 59
def prefixEnd_7104708 : Nat := 4983230072969 + 3 ^ 40 * 7104708 * 2
def baseEnd_7104708 : Nat := 1216043371281231343658683

theorem tailTrace_7104708 : CollatzResearch.WordTrace tailWord_7104708 prefixEnd_7104708 1216043371281231343658683 := by
  unfold tailWord_7104708
  simp only [CollatzResearch.WordTrace]
  refine ⟨129564994572431889184397389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172753326096575852245863185 129564994572431889184397389)
  ·
    refine ⟨48586872964661958444149021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129564994572431889184397389 48586872964661958444149021)
    ·
      refine ⟨18220077361748234416555883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48586872964661958444149021 18220077361748234416555883)
      ·
        refine ⟨27330116042622351624833825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18220077361748234416555883 27330116042622351624833825)
        ·
          refine ⟨20497587031966763718625369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27330116042622351624833825 20497587031966763718625369)
          ·
            refine ⟨15373190273975072788969027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20497587031966763718625369 15373190273975072788969027)
            ·
              refine ⟨23059785410962609183453541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15373190273975072788969027 23059785410962609183453541)
              ·
                refine ⟨4323709764555489221897539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23059785410962609183453541 4323709764555489221897539)
                ·
                  refine ⟨6485564646833233832846309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4323709764555489221897539 6485564646833233832846309)
                  ·
                    refine ⟨1216043371281231343658683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6485564646833233832846309 1216043371281231343658683)
                    ·
                      rfl

theorem cell23_7104708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_7104708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7104708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7104708 prefixEnd_7104708 := by exact prefixLift 7104708
  have htrace : WordTrace (prefixWord ++ tailWord_7104708) baseStart_7104708 baseEnd_7104708 := by
    simpa [prefixWord, tailWord_7104708, baseEnd_7104708] using wordTrace_append hprefix tailTrace_7104708
  have hstable : (prefixWord ++ tailWord_7104708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7104708).length < 2 ^ (prefixWord ++ tailWord_7104708).sum := by decide
  have hdescent : baseEnd_7104708 < baseStart_7104708 := by decide
  rcases family_descends (prefixWord ++ tailWord_7104708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7104741 : List Nat := [1, 3, 1, 4, 2, 2, 1, 1, 1, 5, 2]
def baseStart_7104741 : Nat := 118140960795 + 7104741 * 2 ^ 59
def prefixEnd_7104741 : Nat := 4983230072969 + 3 ^ 40 * 7104741 * 2
def baseEnd_7104741 : Nat := 3648147058705292401863397

theorem tailTrace_7104741 : CollatzResearch.WordTrace tailWord_7104741 prefixEnd_7104741 3648147058705292401863397 := by
  unfold tailWord_7104741
  simp only [CollatzResearch.WordTrace]
  refine ⟨259131192753744225004746077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172754128502496150003164051 259131192753744225004746077)
  ·
    refine ⟨97174197282654084376779779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259131192753744225004746077 97174197282654084376779779)
    ·
      refine ⟨145761295923981126565169669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97174197282654084376779779 145761295923981126565169669)
      ·
        refine ⟨27330242985746461230969313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145761295923981126565169669 27330242985746461230969313)
        ·
          refine ⟨20497682239309845923226985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27330242985746461230969313 20497682239309845923226985)
          ·
            refine ⟨15373261679482384442420239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20497682239309845923226985 15373261679482384442420239)
            ·
              refine ⟨23059892519223576663630359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15373261679482384442420239 23059892519223576663630359)
              ·
                refine ⟨34589838778835364995445539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23059892519223576663630359 34589838778835364995445539)
                ·
                  refine ⟨51884758168253047493168309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34589838778835364995445539 51884758168253047493168309)
                  ·
                    refine ⟨4864196078273723202484529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51884758168253047493168309 4864196078273723202484529)
                    ·
                      refine ⟨3648147058705292401863397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4864196078273723202484529 3648147058705292401863397)
                      ·
                        rfl

theorem cell23_7104741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 5, 2].length) (baseStart_7104741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7104741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7104741 prefixEnd_7104741 := by exact prefixLift 7104741
  have htrace : WordTrace (prefixWord ++ tailWord_7104741) baseStart_7104741 baseEnd_7104741 := by
    simpa [prefixWord, tailWord_7104741, baseEnd_7104741] using wordTrace_append hprefix tailTrace_7104741
  have hstable : (prefixWord ++ tailWord_7104741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7104741).length < 2 ^ (prefixWord ++ tailWord_7104741).sum := by decide
  have hdescent : baseEnd_7104741 < baseStart_7104741 := by decide
  rcases family_descends (prefixWord ++ tailWord_7104741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7104747 : List Nat := [1, 1, 1, 1, 2, 5, 1, 4, 1, 6]
def baseStart_7104747 : Nat := 118140960795 + 7104747 * 2 ^ 59
def prefixEnd_7104747 : Nat := 4983230072969 + 3 ^ 40 * 7104747 * 2
def baseEnd_7104747 : Nat := 1216050046529739792796123

theorem tailTrace_7104747 : CollatzResearch.WordTrace tailWord_7104747 prefixEnd_7104747 1216050046529739792796123 := by
  unfold tailWord_7104747
  simp only [CollatzResearch.WordTrace]
  refine ⟨259131411591722488029464495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172754274394481658686309663 259131411591722488029464495)
  ·
    refine ⟨388697117387583732044196743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259131411591722488029464495 388697117387583732044196743)
    ·
      refine ⟨583045676081375598066295115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388697117387583732044196743 583045676081375598066295115)
      ·
        refine ⟨874568514122063397099442673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 583045676081375598066295115 874568514122063397099442673)
        ·
          refine ⟨655926385591547547824582005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 874568514122063397099442673 655926385591547547824582005)
          ·
            refine ⟨61493098649207582608554563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 655926385591547547824582005 61493098649207582608554563)
            ·
              refine ⟨92239647973811373912831845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61493098649207582608554563 92239647973811373912831845)
              ·
                refine ⟨17294933995089632608655971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92239647973811373912831845 17294933995089632608655971)
                ·
                  refine ⟨25942400992634448912983957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17294933995089632608655971 25942400992634448912983957)
                  ·
                    refine ⟨1216050046529739792796123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25942400992634448912983957 1216050046529739792796123)
                    ·
                      rfl

theorem cell23_7104747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 4, 1, 6].length) (baseStart_7104747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7104747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7104747 prefixEnd_7104747 := by exact prefixLift 7104747
  have htrace : WordTrace (prefixWord ++ tailWord_7104747) baseStart_7104747 baseEnd_7104747 := by
    simpa [prefixWord, tailWord_7104747, baseEnd_7104747] using wordTrace_append hprefix tailTrace_7104747
  have hstable : (prefixWord ++ tailWord_7104747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7104747).length < 2 ^ (prefixWord ++ tailWord_7104747).sum := by decide
  have hdescent : baseEnd_7104747 < baseStart_7104747 := by decide
  rcases family_descends (prefixWord ++ tailWord_7104747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7104748 : List Nat := [2, 2, 1, 1, 2, 3, 4, 3, 1, 1, 3]
def baseStart_7104748 : Nat := 118140960795 + 7104748 * 2 ^ 59
def prefixEnd_7104748 : Nat := 4983230072969 + 3 ^ 40 * 7104748 * 2
def baseEnd_7104748 : Nat := 3648150653069873874475865

theorem tailTrace_7104748 : CollatzResearch.WordTrace tailWord_7104748 prefixEnd_7104748 3648150653069873874475865 := by
  unfold tailWord_7104748
  simp only [CollatzResearch.WordTrace]
  refine ⟨129565724032359432600125449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172754298709812576800167265 129565724032359432600125449)
  ·
    refine ⟨97174293024269574450094087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129565724032359432600125449 97174293024269574450094087)
    ·
      refine ⟨145761439536404361675141131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97174293024269574450094087 145761439536404361675141131)
      ·
        refine ⟨218642159304606542512711697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145761439536404361675141131 218642159304606542512711697)
        ·
          refine ⟨163981619478454906884533773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218642159304606542512711697 163981619478454906884533773)
          ·
            refine ⟨61493107304420590081700165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163981619478454906884533773 61493107304420590081700165)
            ·
              refine ⟨11529957619578860640318781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61493107304420590081700165 11529957619578860640318781)
              ·
                refine ⟨4323734107342072740119543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11529957619578860640318781 4323734107342072740119543)
                ·
                  refine ⟨6485601161013109110179315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4323734107342072740119543 6485601161013109110179315)
                  ·
                    refine ⟨9728401741519663665268973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6485601161013109110179315 9728401741519663665268973)
                    ·
                      refine ⟨3648150653069873874475865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9728401741519663665268973 3648150653069873874475865)
                      ·
                        rfl

theorem cell23_7104748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 3, 1, 1, 3].length) (baseStart_7104748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7104748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7104748 prefixEnd_7104748 := by exact prefixLift 7104748
  have htrace : WordTrace (prefixWord ++ tailWord_7104748) baseStart_7104748 baseEnd_7104748 := by
    simpa [prefixWord, tailWord_7104748, baseEnd_7104748] using wordTrace_append hprefix tailTrace_7104748
  have hstable : (prefixWord ++ tailWord_7104748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7104748).length < 2 ^ (prefixWord ++ tailWord_7104748).sum := by decide
  have hdescent : baseEnd_7104748 < baseStart_7104748 := by decide
  rcases family_descends (prefixWord ++ tailWord_7104748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7104751 : List Nat := [1, 1, 2, 1, 6, 1, 4, 1, 1, 5]
def baseStart_7104751 : Nat := 118140960795 + 7104751 * 2 ^ 59
def prefixEnd_7104751 : Nat := 4983230072969 + 3 ^ 40 * 7104751 * 2
def baseEnd_7104751 : Nat := 1216050731170612454246117

theorem tailTrace_7104751 : CollatzResearch.WordTrace tailWord_7104751 prefixEnd_7104751 1216050731170612454246117 := by
  unfold tailWord_7104751
  simp only [CollatzResearch.WordTrace]
  refine ⟨259131557483707996712610107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172754371655805331141740071 259131557483707996712610107)
  ·
    refine ⟨388697336225561995068915161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259131557483707996712610107 388697336225561995068915161)
    ·
      refine ⟨291523002169171496301686371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 388697336225561995068915161 291523002169171496301686371)
      ·
        refine ⟨437284503253757244452529557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291523002169171496301686371 437284503253757244452529557)
        ·
          refine ⟨20497711090019870833712323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 437284503253757244452529557 20497711090019870833712323)
          ·
            refine ⟨30746566635029806250568485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20497711090019870833712323 30746566635029806250568485)
            ·
              refine ⟨5764981244068088671981591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30746566635029806250568485 5764981244068088671981591)
              ·
                refine ⟨8647471866102133007972387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5764981244068088671981591 8647471866102133007972387)
                ·
                  refine ⟨12971207799153199511958581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8647471866102133007972387 12971207799153199511958581)
                  ·
                    refine ⟨1216050731170612454246117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12971207799153199511958581 1216050731170612454246117)
                    ·
                      rfl

theorem cell23_7104751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 4, 1, 1, 5].length) (baseStart_7104751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7104751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7104751 prefixEnd_7104751 := by exact prefixLift 7104751
  have htrace : WordTrace (prefixWord ++ tailWord_7104751) baseStart_7104751 baseEnd_7104751 := by
    simpa [prefixWord, tailWord_7104751, baseEnd_7104751] using wordTrace_append hprefix tailTrace_7104751
  have hstable : (prefixWord ++ tailWord_7104751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7104751).length < 2 ^ (prefixWord ++ tailWord_7104751).sum := by decide
  have hdescent : baseEnd_7104751 < baseStart_7104751 := by decide
  rcases family_descends (prefixWord ++ tailWord_7104751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7104767 : List Nat := [1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 6]
def baseStart_7104767 : Nat := 118140960795 + 7104767 * 2 ^ 59
def prefixEnd_7104767 : Nat := 4983230072969 + 3 ^ 40 * 7104767 * 2
def baseEnd_7104767 : Nat := 3648160409202309300138277

theorem tailTrace_7104767 : CollatzResearch.WordTrace tailWord_7104767 prefixEnd_7104767 3648160409202309300138277 := by
  unfold tailWord_7104767
  simp only [CollatzResearch.WordTrace]
  refine ⟨259132141051650031445192555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172754760701100020963461703 259132141051650031445192555)
  ·
    refine ⟨388698211577475047167788833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259132141051650031445192555 388698211577475047167788833)
    ·
      refine ⟨291523658683106285375841625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 388698211577475047167788833 291523658683106285375841625)
      ·
        refine ⟨218642744012329714031881219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291523658683106285375841625 218642744012329714031881219)
        ·
          refine ⟨327964116018494571047821829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218642744012329714031881219 327964116018494571047821829)
          ·
            refine ⟨61493271753467732071466593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 327964116018494571047821829 61493271753467732071466593)
            ·
              refine ⟨46119953815100799053599945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61493271753467732071466593 46119953815100799053599945)
              ·
                refine ⟨34589965361325599290199959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46119953815100799053599945 34589965361325599290199959)
                ·
                  refine ⟨51884948041988398935299939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34589965361325599290199959 51884948041988398935299939)
                  ·
                    refine ⟨77827422062982598402949909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51884948041988398935299939 77827422062982598402949909)
                    ·
                      refine ⟨3648160409202309300138277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77827422062982598402949909 3648160409202309300138277)
                      ·
                        rfl

theorem cell23_7104767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 6].length) (baseStart_7104767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7104767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7104767 prefixEnd_7104767 := by exact prefixLift 7104767
  have htrace : WordTrace (prefixWord ++ tailWord_7104767) baseStart_7104767 baseEnd_7104767 := by
    simpa [prefixWord, tailWord_7104767, baseEnd_7104767] using wordTrace_append hprefix tailTrace_7104767
  have hstable : (prefixWord ++ tailWord_7104767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7104767).length < 2 ^ (prefixWord ++ tailWord_7104767).sum := by decide
  have hdescent : baseEnd_7104767 < baseStart_7104767 := by decide
  rcases family_descends (prefixWord ++ tailWord_7104767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7104791 : List Nat := [1, 1, 3, 4, 1, 2, 1, 4, 1, 2, 3]
def baseStart_7104791 : Nat := 118140960795 + 7104791 * 2 ^ 59
def prefixEnd_7104791 : Nat := 4983230072969 + 3 ^ 40 * 7104791 * 2
def baseEnd_7104791 : Nat := 3648172732738017206238167

theorem tailTrace_7104791 : CollatzResearch.WordTrace tailWord_7104791 prefixEnd_7104791 3648172732738017206238167 := by
  unfold tailWord_7104791
  simp only [CollatzResearch.WordTrace]
  refine ⟨259133016403563083544066227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172755344269042055696044151 259133016403563083544066227)
  ·
    refine ⟨388699524605344625316099341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259133016403563083544066227 388699524605344625316099341)
    ·
      refine ⟨145762321727004234493537253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 388699524605344625316099341 145762321727004234493537253)
      ·
        refine ⟨27330435323813293967538235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145762321727004234493537253 27330435323813293967538235)
        ·
          refine ⟨40995652985719940951307353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27330435323813293967538235 40995652985719940951307353)
          ·
            refine ⟨30746739739289955713480515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40995652985719940951307353 30746739739289955713480515)
            ·
              refine ⟨46120109608934933570220773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30746739739289955713480515 46120109608934933570220773)
              ·
                refine ⟨8647520551675300044416395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46120109608934933570220773 8647520551675300044416395)
                ·
                  refine ⟨12971280827512950066624593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8647520551675300044416395 12971280827512950066624593)
                  ·
                    refine ⟨9728460620634712549968445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12971280827512950066624593 9728460620634712549968445)
                    ·
                      refine ⟨3648172732738017206238167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9728460620634712549968445 3648172732738017206238167)
                      ·
                        rfl

theorem cell23_7104791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_7104791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7104791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7104791 prefixEnd_7104791 := by exact prefixLift 7104791
  have htrace : WordTrace (prefixWord ++ tailWord_7104791) baseStart_7104791 baseEnd_7104791 := by
    simpa [prefixWord, tailWord_7104791, baseEnd_7104791] using wordTrace_append hprefix tailTrace_7104791
  have hstable : (prefixWord ++ tailWord_7104791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7104791).length < 2 ^ (prefixWord ++ tailWord_7104791).sum := by decide
  have hdescent : baseEnd_7104791 < baseStart_7104791 := by decide
  rcases family_descends (prefixWord ++ tailWord_7104791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7104794 : List Nat := [3, 1, 1, 3, 4, 1, 1, 9]
def baseStart_7104794 : Nat := 118140960795 + 7104794 * 2 ^ 59
def prefixEnd_7104794 : Nat := 4983230072969 + 3 ^ 40 * 7104794 * 2
def baseEnd_7104794 : Nat := 135117565673332618314839

theorem tailTrace_7104794 : CollatzResearch.WordTrace tailWord_7104794 prefixEnd_7104794 135117565673332618314839 := by
  unfold tailWord_7104794
  simp only [CollatzResearch.WordTrace]
  refine ⟨64783281455638053764106359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172755417215034810037616957 64783281455638053764106359)
  ·
    refine ⟨97174922183457080646159539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64783281455638053764106359 97174922183457080646159539)
    ·
      refine ⟨145762383275185620969239309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97174922183457080646159539 145762383275185620969239309)
      ·
        refine ⟨54660893728194607863464741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145762383275185620969239309 54660893728194607863464741)
        ·
          refine ⟨10248917574036488974399639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54660893728194607863464741 10248917574036488974399639)
          ·
            refine ⟨15373376361054733461599459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10248917574036488974399639 15373376361054733461599459)
            ·
              refine ⟨23060064541582100192399189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15373376361054733461599459 23060064541582100192399189)
              ·
                refine ⟨135117565673332618314839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23060064541582100192399189 135117565673332618314839)
                ·
                  rfl

theorem cell23_7104794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 9].length) (baseStart_7104794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7104794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7104794 prefixEnd_7104794 := by exact prefixLift 7104794
  have htrace : WordTrace (prefixWord ++ tailWord_7104794) baseStart_7104794 baseEnd_7104794 := by
    simpa [prefixWord, tailWord_7104794, baseEnd_7104794] using wordTrace_append hprefix tailTrace_7104794
  have hstable : (prefixWord ++ tailWord_7104794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7104794).length < 2 ^ (prefixWord ++ tailWord_7104794).sum := by decide
  have hdescent : baseEnd_7104794 < baseStart_7104794 := by decide
  rcases family_descends (prefixWord ++ tailWord_7104794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7104798 : List Nat := [4, 3, 2, 1, 1, 1, 1, 2, 4, 4]
def baseStart_7104798 : Nat := 118140960795 + 7104798 * 2 ^ 59
def prefixEnd_7104798 : Nat := 4983230072969 + 3 ^ 40 * 7104798 * 2
def baseEnd_7104798 : Nat := 1216058775700866226283545

theorem tailTrace_7104798 : CollatzResearch.WordTrace tailWord_7104798 prefixEnd_7104798 1216058775700866226283545 := by
  unfold tailWord_7104798
  simp only [CollatzResearch.WordTrace]
  refine ⟨32391658964317215467446381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172755514476358482493047365 32391658964317215467446381)
  ·
    refine ⟨12146872111618955800292393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32391658964317215467446381 12146872111618955800292393)
    ·
      refine ⟨9110154083714216850219295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12146872111618955800292393 9110154083714216850219295)
      ·
        refine ⟨13665231125571325275328943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9110154083714216850219295 13665231125571325275328943)
        ·
          refine ⟨20497846688356987912993415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13665231125571325275328943 20497846688356987912993415)
          ·
            refine ⟨30746770032535481869490123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20497846688356987912993415 30746770032535481869490123)
            ·
              refine ⟨46120155048803222804235185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30746770032535481869490123 46120155048803222804235185)
              ·
                refine ⟨34590116286602417103176389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46120155048803222804235185 34590116286602417103176389)
                ·
                  refine ⟨6485646803737953206845573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34590116286602417103176389 6485646803737953206845573)
                  ·
                    refine ⟨1216058775700866226283545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6485646803737953206845573 1216058775700866226283545)
                    ·
                      rfl

theorem cell23_7104798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_7104798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7104798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7104798 prefixEnd_7104798 := by exact prefixLift 7104798
  have htrace : WordTrace (prefixWord ++ tailWord_7104798) baseStart_7104798 baseEnd_7104798 := by
    simpa [prefixWord, tailWord_7104798, baseEnd_7104798] using wordTrace_append hprefix tailTrace_7104798
  have hstable : (prefixWord ++ tailWord_7104798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7104798).length < 2 ^ (prefixWord ++ tailWord_7104798).sum := by decide
  have hdescent : baseEnd_7104798 < baseStart_7104798 := by decide
  rcases family_descends (prefixWord ++ tailWord_7104798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7104821 : List Nat := [1, 3, 3, 1, 2, 1, 1, 3, 4, 1, 3]
def baseStart_7104821 : Nat := 118140960795 + 7104821 * 2 ^ 59
def prefixEnd_7104821 : Nat := 4983230072969 + 3 ^ 40 * 7104821 * 2
def baseEnd_7104821 : Nat := 3648188137157652088863029

theorem tailTrace_7104821 : CollatzResearch.WordTrace tailWord_7104821 prefixEnd_7104821 3648188137157652088863029 := by
  unfold tailWord_7104821
  simp only [CollatzResearch.WordTrace]
  refine ⟨259134110593454398667658317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172756073728969599111772211 259134110593454398667658317)
  ·
    refine ⟨97175291472545399500371869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259134110593454398667658317 97175291472545399500371869)
    ·
      refine ⟨36440734302204524812639451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97175291472545399500371869 36440734302204524812639451)
      ·
        refine ⟨54661101453306787218959177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36440734302204524812639451 54661101453306787218959177)
        ·
          refine ⟨40995826089980090414219383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54661101453306787218959177 40995826089980090414219383)
          ·
            refine ⟨61493739134970135621329075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40995826089980090414219383 61493739134970135621329075)
            ·
              refine ⟨92240608702455203431993613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61493739134970135621329075 92240608702455203431993613)
              ·
                refine ⟨34590228263420701286997605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92240608702455203431993613 34590228263420701286997605)
                ·
                  refine ⟨6485667799391381491312051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34590228263420701286997605 6485667799391381491312051)
                  ·
                    refine ⟨9728501699087072236968077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6485667799391381491312051 9728501699087072236968077)
                    ·
                      refine ⟨3648188137157652088863029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9728501699087072236968077 3648188137157652088863029)
                      ·
                        rfl

theorem cell23_7104821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 4, 1, 3].length) (baseStart_7104821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7104821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7104821 prefixEnd_7104821 := by exact prefixLift 7104821
  have htrace : WordTrace (prefixWord ++ tailWord_7104821) baseStart_7104821 baseEnd_7104821 := by
    simpa [prefixWord, tailWord_7104821, baseEnd_7104821] using wordTrace_append hprefix tailTrace_7104821
  have hstable : (prefixWord ++ tailWord_7104821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7104821).length < 2 ^ (prefixWord ++ tailWord_7104821).sum := by decide
  have hdescent : baseEnd_7104821 < baseStart_7104821 := by decide
  rcases family_descends (prefixWord ++ tailWord_7104821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7104831 : List Nat := [1, 1, 2, 2, 4, 1, 2, 2, 3, 3, 2]
def baseStart_7104831 : Nat := 118140960795 + 7104831 * 2 ^ 59
def prefixEnd_7104831 : Nat := 4983230072969 + 3 ^ 40 * 7104831 * 2
def baseEnd_7104831 : Nat := 3648193271964197049737983

theorem tailTrace_7104831 : CollatzResearch.WordTrace tailWord_7104831 prefixEnd_7104831 3648193271964197049737983 := by
  unfold tailWord_7104831
  simp only [CollatzResearch.WordTrace]
  refine ⟨259134475323418170375522347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172756316882278780250348231 259134475323418170375522347)
  ·
    refine ⟨388701712985127255563283521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259134475323418170375522347 388701712985127255563283521)
    ·
      refine ⟨291526284738845441672462641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 388701712985127255563283521 291526284738845441672462641)
      ·
        refine ⟨218644713554134081254346981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291526284738845441672462641 218644713554134081254346981)
        ·
          refine ⟨40995883791400140235190059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 218644713554134081254346981 40995883791400140235190059)
          ·
            refine ⟨61493825687100210352785089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40995883791400140235190059 61493825687100210352785089)
            ·
              refine ⟨46120369265325157764588817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61493825687100210352785089 46120369265325157764588817)
              ·
                refine ⟨34590276948993868323441613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46120369265325157764588817 34590276948993868323441613)
                ·
                  refine ⟨12971353855872700621290605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34590276948993868323441613 12971353855872700621290605)
                  ·
                    refine ⟨4864257695952262732983977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12971353855872700621290605 4864257695952262732983977)
                    ·
                      refine ⟨3648193271964197049737983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4864257695952262732983977 3648193271964197049737983)
                      ·
                        rfl

theorem cell23_7104831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 3, 3, 2].length) (baseStart_7104831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7104831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7104831 prefixEnd_7104831 := by exact prefixLift 7104831
  have htrace : WordTrace (prefixWord ++ tailWord_7104831) baseStart_7104831 baseEnd_7104831 := by
    simpa [prefixWord, tailWord_7104831, baseEnd_7104831] using wordTrace_append hprefix tailTrace_7104831
  have hstable : (prefixWord ++ tailWord_7104831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7104831).length < 2 ^ (prefixWord ++ tailWord_7104831).sum := by decide
  have hdescent : baseEnd_7104831 < baseStart_7104831 := by decide
  rcases family_descends (prefixWord ++ tailWord_7104831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7104848 : List Nat := [2, 1, 1, 1, 1, 6, 3, 2, 1, 3, 2]
def baseStart_7104848 : Nat := 118140960795 + 7104848 * 2 ^ 59
def prefixEnd_7104848 : Nat := 4983230072969 + 3 ^ 40 * 7104848 * 2
def baseEnd_7104848 : Nat := 3648202001135323483225405

theorem tailTrace_7104848 : CollatzResearch.WordTrace tailWord_7104848 prefixEnd_7104848 3648202001135323483225405 := by
  unfold tailWord_7104848
  simp only [CollatzResearch.WordTrace]
  refine ⟨129567547682178291139445599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172756730242904388185927465 129567547682178291139445599)
  ·
    refine ⟨194351321523267436709168399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129567547682178291139445599 194351321523267436709168399)
    ·
      refine ⟨291526982284901155063752599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194351321523267436709168399 291526982284901155063752599)
      ·
        refine ⟨437290473427351732595628899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291526982284901155063752599 437290473427351732595628899)
        ·
          refine ⟨655935710141027598893443349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 437290473427351732595628899 655935710141027598893443349)
          ·
            refine ⟨30746986412860668698130157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 655935710141027598893443349 30746986412860668698130157)
            ·
              refine ⟨11530119904822750761798809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30746986412860668698130157 11530119904822750761798809)
              ·
                refine ⟨8647589928617063071349107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11530119904822750761798809 8647589928617063071349107)
                ·
                  refine ⟨12971384892925594607023661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8647589928617063071349107 12971384892925594607023661)
                  ·
                    refine ⟨4864269334847097977633873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12971384892925594607023661 4864269334847097977633873)
                    ·
                      refine ⟨3648202001135323483225405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4864269334847097977633873 3648202001135323483225405)
                      ·
                        rfl

theorem cell23_7104848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 2, 1, 3, 2].length) (baseStart_7104848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7104848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7104848 prefixEnd_7104848 := by exact prefixLift 7104848
  have htrace : WordTrace (prefixWord ++ tailWord_7104848) baseStart_7104848 baseEnd_7104848 := by
    simpa [prefixWord, tailWord_7104848, baseEnd_7104848] using wordTrace_append hprefix tailTrace_7104848
  have hstable : (prefixWord ++ tailWord_7104848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7104848).length < 2 ^ (prefixWord ++ tailWord_7104848).sum := by decide
  have hdescent : baseEnd_7104848 < baseStart_7104848 := by decide
  rcases family_descends (prefixWord ++ tailWord_7104848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7104929 : List Nat := [1, 2, 3, 5, 1, 2, 1, 2, 2, 2, 2]
def baseStart_7104929 : Nat := 118140960795 + 7104929 * 2 ^ 59
def prefixEnd_7104929 : Nat := 4983230072969 + 3 ^ 40 * 7104929 * 2
def baseEnd_7104929 : Nat := 3648243593068337666312533

theorem tailTrace_7104929 : CollatzResearch.WordTrace tailWord_7104929 prefixEnd_7104929 3648243593068337666312533 := by
  unfold tailWord_7104929
  simp only [CollatzResearch.WordTrace]
  refine ⟨259138049677063133112589841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172758699784708755408393227 259138049677063133112589841)
  ·
    refine ⟨194353537257797349834442381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259138049677063133112589841 194353537257797349834442381)
    ·
      refine ⟨72882576471674006187915893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194353537257797349834442381 72882576471674006187915893)
      ·
        refine ⟨6832741544219438080117115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72882576471674006187915893 6832741544219438080117115)
        ·
          refine ⟨10249112316329157120175673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6832741544219438080117115 10249112316329157120175673)
          ·
            refine ⟨7686834237246867840131755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10249112316329157120175673 7686834237246867840131755)
            ·
              refine ⟨11530251355870301760197633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7686834237246867840131755 11530251355870301760197633)
              ·
                refine ⟨8647688516902726320148225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11530251355870301760197633 8647688516902726320148225)
                ·
                  refine ⟨6485766387677044740111169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8647688516902726320148225 6485766387677044740111169)
                  ·
                    refine ⟨4864324790757783555083377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6485766387677044740111169 4864324790757783555083377)
                    ·
                      refine ⟨3648243593068337666312533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4864324790757783555083377 3648243593068337666312533)
                      ·
                        rfl

theorem cell23_7104929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_7104929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7104929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7104929 prefixEnd_7104929 := by exact prefixLift 7104929
  have htrace : WordTrace (prefixWord ++ tailWord_7104929) baseStart_7104929 baseEnd_7104929 := by
    simpa [prefixWord, tailWord_7104929, baseEnd_7104929] using wordTrace_append hprefix tailTrace_7104929
  have hstable : (prefixWord ++ tailWord_7104929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7104929).length < 2 ^ (prefixWord ++ tailWord_7104929).sum := by decide
  have hdescent : baseEnd_7104929 < baseStart_7104929 := by decide
  rcases family_descends (prefixWord ++ tailWord_7104929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7104971 : List Nat := [1, 1, 1, 1, 3, 3, 1, 5, 2, 2, 3]
def baseStart_7104971 : Nat := 118140960795 + 7104971 * 2 ^ 59
def prefixEnd_7104971 : Nat := 4983230072969 + 3 ^ 40 * 7104971 * 2
def baseEnd_7104971 : Nat := 3648265159255826501987339

theorem tailTrace_7104971 : CollatzResearch.WordTrace tailWord_7104971 prefixEnd_7104971 3648265159255826501987339 := by
  unfold tailWord_7104971
  simp only [CollatzResearch.WordTrace]
  refine ⟨259139581542910974285618767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172759721028607316190412511 259139581542910974285618767)
  ·
    refine ⟨388709372314366461428428151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259139581542910974285618767 388709372314366461428428151)
    ·
      refine ⟨583064058471549692142642227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388709372314366461428428151 583064058471549692142642227)
      ·
        refine ⟨874596087707324538213963341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 583064058471549692142642227 874596087707324538213963341)
        ·
          refine ⟨327973532890246701830236253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 874596087707324538213963341 327973532890246701830236253)
          ·
            refine ⟨122990074833842513186338595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 327973532890246701830236253 122990074833842513186338595)
            ·
              refine ⟨184485112250763769779507893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122990074833842513186338595 184485112250763769779507893)
              ·
                refine ⟨17295479273509103416828865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 184485112250763769779507893 17295479273509103416828865)
                ·
                  refine ⟨12971609455131827562621649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17295479273509103416828865 12971609455131827562621649)
                  ·
                    refine ⟨9728707091348870671966237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12971609455131827562621649 9728707091348870671966237)
                    ·
                      refine ⟨3648265159255826501987339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9728707091348870671966237 3648265159255826501987339)
                      ·
                        rfl

theorem cell23_7104971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 5, 2, 2, 3].length) (baseStart_7104971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7104971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7104971 prefixEnd_7104971 := by exact prefixLift 7104971
  have htrace : WordTrace (prefixWord ++ tailWord_7104971) baseStart_7104971 baseEnd_7104971 := by
    simpa [prefixWord, tailWord_7104971, baseEnd_7104971] using wordTrace_append hprefix tailTrace_7104971
  have hstable : (prefixWord ++ tailWord_7104971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7104971).length < 2 ^ (prefixWord ++ tailWord_7104971).sum := by decide
  have hdescent : baseEnd_7104971 < baseStart_7104971 := by decide
  rcases family_descends (prefixWord ++ tailWord_7104971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7104995 : List Nat := [1, 1, 1, 6, 3, 2, 1, 1, 3, 4]
def baseStart_7104995 : Nat := 118140960795 + 7104995 * 2 ^ 59
def prefixEnd_7104995 : Nat := 4983230072969 + 3 ^ 40 * 7104995 * 2
def baseEnd_7104995 : Nat := 1216092494263844802695743

theorem tailTrace_7104995 : CollatzResearch.WordTrace tailWord_7104995 prefixEnd_7104995 1216092494263844802695743 := by
  unfold tailWord_7104995
  simp only [CollatzResearch.WordTrace]
  refine ⟨259140456894824026384492439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172760304596549350922994959 259140456894824026384492439)
  ·
    refine ⟨388710685342236039576738659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259140456894824026384492439 388710685342236039576738659)
    ·
      refine ⟨583066028013354059365107989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388710685342236039576738659 583066028013354059365107989)
      ·
        refine ⟨27331220063125971532739437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 583066028013354059365107989 27331220063125971532739437)
        ·
          refine ⟨10249207523672239324777289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27331220063125971532739437 10249207523672239324777289)
          ·
            refine ⟨7686905642754179493582967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10249207523672239324777289 7686905642754179493582967)
            ·
              refine ⟨11530358464131269240374451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7686905642754179493582967 11530358464131269240374451)
              ·
                refine ⟨17295537696196903860561677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11530358464131269240374451 17295537696196903860561677)
                ·
                  refine ⟨6485826636073838947710629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17295537696196903860561677 6485826636073838947710629)
                  ·
                    refine ⟨1216092494263844802695743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6485826636073838947710629 1216092494263844802695743)
                    ·
                      rfl

theorem cell23_7104995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 1, 3, 4].length) (baseStart_7104995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7104995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7104995 prefixEnd_7104995 := by exact prefixLift 7104995
  have htrace : WordTrace (prefixWord ++ tailWord_7104995) baseStart_7104995 baseEnd_7104995 := by
    simpa [prefixWord, tailWord_7104995, baseEnd_7104995] using wordTrace_append hprefix tailTrace_7104995
  have hstable : (prefixWord ++ tailWord_7104995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7104995).length < 2 ^ (prefixWord ++ tailWord_7104995).sum := by decide
  have hdescent : baseEnd_7104995 < baseStart_7104995 := by decide
  rcases family_descends (prefixWord ++ tailWord_7104995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7105021 : List Nat := [1, 4, 1, 1, 1, 3, 3, 1, 3, 5]
def baseStart_7105021 : Nat := 118140960795 + 7105021 * 2 ^ 59
def prefixEnd_7105021 : Nat := 4983230072969 + 3 ^ 40 * 7105021 * 2
def baseEnd_7105021 : Nat := 1216096944429517102120703

theorem tailTrace_7105021 : CollatzResearch.WordTrace tailWord_7105021 prefixEnd_7105021 1216096944429517102120703 := by
  unfold tailWord_7105021
  simp only [CollatzResearch.WordTrace]
  refine ⟨259141405192729832824938917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172760936795153221883292611 259141405192729832824938917)
  ·
    refine ⟨48589013473636843654676047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 259141405192729832824938917 48589013473636843654676047)
    ·
      refine ⟨72883520210455265482014071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48589013473636843654676047 72883520210455265482014071)
      ·
        refine ⟨109325280315682898223021107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72883520210455265482014071 109325280315682898223021107)
        ·
          refine ⟨163987920473524347334531661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109325280315682898223021107 163987920473524347334531661)
          ·
            refine ⟨61495470177571630250449373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163987920473524347334531661 61495470177571630250449373)
            ·
              refine ⟨23060801316589361343918515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61495470177571630250449373 23060801316589361343918515)
              ·
                refine ⟨34591201974884042015877773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23060801316589361343918515 34591201974884042015877773)
                ·
                  refine ⟨12971700740581515755954165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34591201974884042015877773 12971700740581515755954165)
                  ·
                    refine ⟨1216096944429517102120703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12971700740581515755954165 1216096944429517102120703)
                    ·
                      rfl

theorem cell23_7105021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 3, 5].length) (baseStart_7105021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7105021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7105021 prefixEnd_7105021 := by exact prefixLift 7105021
  have htrace : WordTrace (prefixWord ++ tailWord_7105021) baseStart_7105021 baseEnd_7105021 := by
    simpa [prefixWord, tailWord_7105021, baseEnd_7105021] using wordTrace_append hprefix tailTrace_7105021
  have hstable : (prefixWord ++ tailWord_7105021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7105021).length < 2 ^ (prefixWord ++ tailWord_7105021).sum := by decide
  have hdescent : baseEnd_7105021 < baseStart_7105021 := by decide
  rcases family_descends (prefixWord ++ tailWord_7105021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7105052 : List Nat := [2, 2, 3, 1, 2, 3, 1, 4, 1, 1, 3]
def baseStart_7105052 : Nat := 118140960795 + 7105052 * 2 ^ 59
def prefixEnd_7105052 : Nat := 4983230072969 + 3 ^ 40 * 7105052 * 2
def baseEnd_7105052 : Nat := 3648306751188840685074467

theorem tailTrace_7105052 : CollatzResearch.WordTrace tailWord_7105052 prefixEnd_7105052 3648306751188840685074467 := by
  unfold tailWord_7105052
  simp only [CollatzResearch.WordTrace]
  refine ⟨129571267927808762559658705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172761690570411683412878273 129571267927808762559658705)
  ·
    refine ⟨97178450945856571919744029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129571267927808762559658705 97178450945856571919744029)
    ·
      refine ⟨36441919104696214469904011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97178450945856571919744029 36441919104696214469904011)
      ·
        refine ⟨54662878657044321704856017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36441919104696214469904011 54662878657044321704856017)
        ·
          refine ⟨40997158992783241278642013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54662878657044321704856017 40997158992783241278642013)
          ·
            refine ⟨15373934622293715479490755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40997158992783241278642013 15373934622293715479490755)
            ·
              refine ⟨23060901933440573219236133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15373934622293715479490755 23060901933440573219236133)
              ·
                refine ⟨4323919112520107478606775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23060901933440573219236133 4323919112520107478606775)
                ·
                  refine ⟨6485878668780161217910163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4323919112520107478606775 6485878668780161217910163)
                  ·
                    refine ⟨9728818003170241826865245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6485878668780161217910163 9728818003170241826865245)
                    ·
                      refine ⟨3648306751188840685074467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9728818003170241826865245 3648306751188840685074467)
                      ·
                        rfl

theorem cell23_7105052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 4, 1, 1, 3].length) (baseStart_7105052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7105052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7105052 prefixEnd_7105052 := by exact prefixLift 7105052
  have htrace : WordTrace (prefixWord ++ tailWord_7105052) baseStart_7105052 baseEnd_7105052 := by
    simpa [prefixWord, tailWord_7105052, baseEnd_7105052] using wordTrace_append hprefix tailTrace_7105052
  have hstable : (prefixWord ++ tailWord_7105052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7105052).length < 2 ^ (prefixWord ++ tailWord_7105052).sum := by decide
  have hdescent : baseEnd_7105052 < baseStart_7105052 := by decide
  rcases family_descends (prefixWord ++ tailWord_7105052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7105058 : List Nat := [3, 3, 1, 1, 1, 1, 1, 2, 2, 6, 2]
def baseStart_7105058 : Nat := 118140960795 + 7105058 * 2 ^ 59
def prefixEnd_7105058 : Nat := 4983230072969 + 3 ^ 40 * 7105058 * 2
def baseEnd_7105058 : Nat := 3648309832072767661599439

theorem tailTrace_7105058 : CollatzResearch.WordTrace tailWord_7105058 prefixEnd_7105058 3648309832072767661599439 := by
  unfold tailWord_7105058
  simp only [CollatzResearch.WordTrace]
  refine ⟨64785688673398947036008957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172761836462397192096023885 64785688673398947036008957)
  ·
    refine ⟨24294633252524605138503359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64785688673398947036008957 24294633252524605138503359)
    ·
      refine ⟨36441949878786907707755039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24294633252524605138503359 36441949878786907707755039)
      ·
        refine ⟨54662924818180361561632559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36441949878786907707755039 54662924818180361561632559)
        ·
          refine ⟨81994387227270542342448839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54662924818180361561632559 81994387227270542342448839)
          ·
            refine ⟨122991580840905813513673259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81994387227270542342448839 122991580840905813513673259)
            ·
              refine ⟨184487371261358720270509889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122991580840905813513673259 184487371261358720270509889)
              ·
                refine ⟨138365528446019040202882417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184487371261358720270509889 138365528446019040202882417)
                ·
                  refine ⟨103774146334514280152161813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 138365528446019040202882417 103774146334514280152161813)
                  ·
                    refine ⟨4864413109430356882132585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 103774146334514280152161813 4864413109430356882132585)
                    ·
                      refine ⟨3648309832072767661599439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4864413109430356882132585 3648309832072767661599439)
                      ·
                        rfl

theorem cell23_7105058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 2, 6, 2].length) (baseStart_7105058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7105058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7105058 prefixEnd_7105058 := by exact prefixLift 7105058
  have htrace : WordTrace (prefixWord ++ tailWord_7105058) baseStart_7105058 baseEnd_7105058 := by
    simpa [prefixWord, tailWord_7105058, baseEnd_7105058] using wordTrace_append hprefix tailTrace_7105058
  have hstable : (prefixWord ++ tailWord_7105058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7105058).length < 2 ^ (prefixWord ++ tailWord_7105058).sum := by decide
  have hdescent : baseEnd_7105058 < baseStart_7105058 := by decide
  rcases family_descends (prefixWord ++ tailWord_7105058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7105061 : List Nat := [1, 3, 1, 2, 2, 1, 2, 4, 1, 1, 5]
def baseStart_7105061 : Nat := 118140960795 + 7105061 * 2 ^ 59
def prefixEnd_7105061 : Nat := 4983230072969 + 3 ^ 40 * 7105061 * 2
def baseEnd_7105061 : Nat := 3648311372514731149861925

theorem tailTrace_7105061 : CollatzResearch.WordTrace tailWord_7105061 prefixEnd_7105061 3648311372514731149861925 := by
  unfold tailWord_7105061
  simp only [CollatzResearch.WordTrace]
  refine ⟨259142864112584919656395037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172761909408389946437596691 259142864112584919656395037)
  ·
    refine ⟨97178574042219344871148139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259142864112584919656395037 97178574042219344871148139)
    ·
      refine ⟨145767861063329017306722209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97178574042219344871148139 145767861063329017306722209)
      ·
        refine ⟨109325895797496762980041657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145767861063329017306722209 109325895797496762980041657)
        ·
          refine ⟨81994421848122572235031243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109325895797496762980041657 81994421848122572235031243)
          ·
            refine ⟨122991632772183858352546865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81994421848122572235031243 122991632772183858352546865)
            ·
              refine ⟨92243724579137893764410149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122991632772183858352546865 92243724579137893764410149)
              ·
                refine ⟨17295698358588355080826903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92243724579137893764410149 17295698358588355080826903)
                ·
                  refine ⟨25943547537882532621240355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17295698358588355080826903 25943547537882532621240355)
                  ·
                    refine ⟨38915321306823798931860533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25943547537882532621240355 38915321306823798931860533)
                    ·
                      refine ⟨3648311372514731149861925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38915321306823798931860533 3648311372514731149861925)
                      ·
                        rfl

theorem cell23_7105061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 4, 1, 1, 5].length) (baseStart_7105061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7105061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7105061 prefixEnd_7105061 := by exact prefixLift 7105061
  have htrace : WordTrace (prefixWord ++ tailWord_7105061) baseStart_7105061 baseEnd_7105061 := by
    simpa [prefixWord, tailWord_7105061, baseEnd_7105061] using wordTrace_append hprefix tailTrace_7105061
  have hstable : (prefixWord ++ tailWord_7105061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7105061).length < 2 ^ (prefixWord ++ tailWord_7105061).sum := by decide
  have hdescent : baseEnd_7105061 < baseStart_7105061 := by decide
  rcases family_descends (prefixWord ++ tailWord_7105061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7105075 : List Nat := [1, 1, 1, 2, 4, 2, 3, 2, 3, 2, 2]
def baseStart_7105075 : Nat := 118140960795 + 7105075 * 2 ^ 59
def prefixEnd_7105075 : Nat := 4983230072969 + 3 ^ 40 * 7105075 * 2
def baseEnd_7105075 : Nat := 3648318561243894095086861

theorem tailTrace_7105075 : CollatzResearch.WordTrace tailWord_7105075 prefixEnd_7105075 3648318561243894095086861 := by
  unfold tailWord_7105075
  simp only [CollatzResearch.WordTrace]
  refine ⟨259143374734534200047404679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172762249823022800031603119 259143374734534200047404679)
  ·
    refine ⟨388715062101801300071107019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259143374734534200047404679 388715062101801300071107019)
    ·
      refine ⟨583072593152701950106660529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388715062101801300071107019 583072593152701950106660529)
      ·
        refine ⟨437304444864526462579995397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 583072593152701950106660529 437304444864526462579995397)
        ·
          refine ⟨81994583412098711733749137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 437304444864526462579995397 81994583412098711733749137)
          ·
            refine ⟨61495937559074033800311853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81994583412098711733749137 61495937559074033800311853)
            ·
              refine ⟨23060976584652762675116945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61495937559074033800311853 23060976584652762675116945)
              ·
                refine ⟨17295732438489572006337709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23060976584652762675116945 17295732438489572006337709)
                ·
                  refine ⟨6485899664433589502376641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17295732438489572006337709 6485899664433589502376641)
                  ·
                    refine ⟨4864424748325192126782481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6485899664433589502376641 4864424748325192126782481)
                    ·
                      refine ⟨3648318561243894095086861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4864424748325192126782481 3648318561243894095086861)
                      ·
                        rfl

theorem cell23_7105075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 2, 3, 2, 2].length) (baseStart_7105075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7105075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7105075 prefixEnd_7105075 := by exact prefixLift 7105075
  have htrace : WordTrace (prefixWord ++ tailWord_7105075) baseStart_7105075 baseEnd_7105075 := by
    simpa [prefixWord, tailWord_7105075, baseEnd_7105075] using wordTrace_append hprefix tailTrace_7105075
  have hstable : (prefixWord ++ tailWord_7105075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7105075).length < 2 ^ (prefixWord ++ tailWord_7105075).sum := by decide
  have hdescent : baseEnd_7105075 < baseStart_7105075 := by decide
  rcases family_descends (prefixWord ++ tailWord_7105075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7105086 : List Nat := [4, 2, 1, 4, 1, 1, 2, 3, 1, 1, 3]
def baseStart_7105086 : Nat := 118140960795 + 7105086 * 2 ^ 59
def prefixEnd_7105086 : Nat := 4983230072969 + 3 ^ 40 * 7105086 * 2
def baseEnd_7105086 : Nat := 3648324209531093552049311

theorem tailTrace_7105086 : CollatzResearch.WordTrace tailWord_7105086 prefixEnd_7105086 3648324209531093552049311 := by
  unfold tailWord_7105086
  simp only [CollatzResearch.WordTrace]
  refine ⟨32392971992186793615756889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172762517291662899284036741 32392971992186793615756889)
  ·
    refine ⟨24294728994140095211817667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32392971992186793615756889 24294728994140095211817667)
    ·
      refine ⟨36442093491210142817726501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24294728994140095211817667 36442093491210142817726501)
      ·
        refine ⟨6832892529601901778323719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36442093491210142817726501 6832892529601901778323719)
        ·
          refine ⟨10249338794402852667485579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6832892529601901778323719 10249338794402852667485579)
          ·
            refine ⟨15374008191604279001228369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10249338794402852667485579 15374008191604279001228369)
            ·
              refine ⟨11530506143703209250921277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15374008191604279001228369 11530506143703209250921277)
              ·
                refine ⟨4323939803888703469095479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11530506143703209250921277 4323939803888703469095479)
                ·
                  refine ⟨6485909705833055203643219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4323939803888703469095479 6485909705833055203643219)
                  ·
                    refine ⟨9728864558749582805464829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6485909705833055203643219 9728864558749582805464829)
                    ·
                      refine ⟨3648324209531093552049311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9728864558749582805464829 3648324209531093552049311)
                      ·
                        rfl

theorem cell23_7105086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_7105086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7105086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7105086 prefixEnd_7105086 := by exact prefixLift 7105086
  have htrace : WordTrace (prefixWord ++ tailWord_7105086) baseStart_7105086 baseEnd_7105086 := by
    simpa [prefixWord, tailWord_7105086, baseEnd_7105086] using wordTrace_append hprefix tailTrace_7105086
  have hstable : (prefixWord ++ tailWord_7105086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7105086).length < 2 ^ (prefixWord ++ tailWord_7105086).sum := by decide
  have hdescent : baseEnd_7105086 < baseStart_7105086 := by decide
  rcases family_descends (prefixWord ++ tailWord_7105086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7105095 : List Nat := [1, 1, 4, 1, 4, 2, 1, 3, 1, 2, 3]
def baseStart_7105095 : Nat := 118140960795 + 7105095 * 2 ^ 59
def prefixEnd_7105095 : Nat := 4983230072969 + 3 ^ 40 * 7105095 * 2
def baseEnd_7105095 : Nat := 3648328830856984016836769

theorem tailTrace_7105095 : CollatzResearch.WordTrace tailWord_7105095 prefixEnd_7105095 3648328830856984016836769 := by
  unfold tailWord_7105095
  simp only [CollatzResearch.WordTrace]
  refine ⟨259144104194461743463132739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172762736129641162308755159 259144104194461743463132739)
  ·
    refine ⟨388716156291692615194699109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259144104194461743463132739 388716156291692615194699109)
    ·
      refine ⟨72884279304692365349006083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 388716156291692615194699109 72884279304692365349006083)
      ·
        refine ⟨109326418957038548023509125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72884279304692365349006083 109326418957038548023509125)
        ·
          refine ⟨20498703554444727754407961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109326418957038548023509125 20498703554444727754407961)
          ·
            refine ⟨15374027665833545815805971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20498703554444727754407961 15374027665833545815805971)
            ·
              refine ⟨23061041498750318723708957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15374027665833545815805971 23061041498750318723708957)
              ·
                refine ⟨8647890562031369521390859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23061041498750318723708957 8647890562031369521390859)
                ·
                  refine ⟨12971835843047054282086289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8647890562031369521390859 12971835843047054282086289)
                  ·
                    refine ⟨9728876882285290711564717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12971835843047054282086289 9728876882285290711564717)
                    ·
                      refine ⟨3648328830856984016836769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9728876882285290711564717 3648328830856984016836769)
                      ·
                        rfl

theorem cell23_7105095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 3, 1, 2, 3].length) (baseStart_7105095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7105095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7105095 prefixEnd_7105095 := by exact prefixLift 7105095
  have htrace : WordTrace (prefixWord ++ tailWord_7105095) baseStart_7105095 baseEnd_7105095 := by
    simpa [prefixWord, tailWord_7105095, baseEnd_7105095] using wordTrace_append hprefix tailTrace_7105095
  have hstable : (prefixWord ++ tailWord_7105095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7105095).length < 2 ^ (prefixWord ++ tailWord_7105095).sum := by decide
  have hdescent : baseEnd_7105095 < baseStart_7105095 := by decide
  rcases family_descends (prefixWord ++ tailWord_7105095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7105135 : List Nat := [1, 1, 2, 1, 3, 2, 3, 4, 1, 3, 2]
def baseStart_7105135 : Nat := 118140960795 + 7105135 * 2 ^ 59
def prefixEnd_7105135 : Nat := 4983230072969 + 3 ^ 40 * 7105135 * 2
def baseEnd_7105135 : Nat := 3648349370083163860336585

theorem tailTrace_7105135 : CollatzResearch.WordTrace tailWord_7105135 prefixEnd_7105135 3648349370083163860336585 := by
  unfold tailWord_7105135
  simp only [CollatzResearch.WordTrace]
  refine ⟨259145563114316830294588859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172763708742877886863059239 259145563114316830294588859)
  ·
    refine ⟨388718344671475245441883289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259145563114316830294588859 388718344671475245441883289)
    ·
      refine ⟨291538758503606434081412467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 388718344671475245441883289 291538758503606434081412467)
      ·
        refine ⟨437308137755409651122118701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291538758503606434081412467 437308137755409651122118701)
        ·
          refine ⟨163990551658278619170794513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 437308137755409651122118701 163990551658278619170794513)
          ·
            refine ⟨122992913743708964378095885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163990551658278619170794513 122992913743708964378095885)
            ·
              refine ⟨46122342653890861641785957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122992913743708964378095885 46122342653890861641785957)
              ·
                refine ⟨8647939247604536557834867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46122342653890861641785957 8647939247604536557834867)
                ·
                  refine ⟨12971908871406804836752301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8647939247604536557834867 12971908871406804836752301)
                  ·
                    refine ⟨4864465826777551813782113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12971908871406804836752301 4864465826777551813782113)
                    ·
                      refine ⟨3648349370083163860336585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4864465826777551813782113 3648349370083163860336585)
                      ·
                        rfl

theorem cell23_7105135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 4, 1, 3, 2].length) (baseStart_7105135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7105135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7105135 prefixEnd_7105135 := by exact prefixLift 7105135
  have htrace : WordTrace (prefixWord ++ tailWord_7105135) baseStart_7105135 baseEnd_7105135 := by
    simpa [prefixWord, tailWord_7105135, baseEnd_7105135] using wordTrace_append hprefix tailTrace_7105135
  have hstable : (prefixWord ++ tailWord_7105135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7105135).length < 2 ^ (prefixWord ++ tailWord_7105135).sum := by decide
  have hdescent : baseEnd_7105135 < baseStart_7105135 := by decide
  rcases family_descends (prefixWord ++ tailWord_7105135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7105182 : List Nat := [4, 3, 1, 1, 1, 1, 2, 3, 1, 4, 2]
def baseStart_7105182 : Nat := 118140960795 + 7105182 * 2 ^ 59
def prefixEnd_7105182 : Nat := 4983230072969 + 3 ^ 40 * 7105182 * 2
def baseEnd_7105182 : Nat := 3648373503673925176448869

theorem tailTrace_7105182 : CollatzResearch.WordTrace tailWord_7105182 prefixEnd_7105182 3648373503673925176448869 := by
  unfold tailWord_7105182
  simp only [CollatzResearch.WordTrace]
  refine ⟨32393409668143319665193725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172764851563431038214366533 32393409668143319665193725)
  ·
    refine ⟨12147528625553744874447647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32393409668143319665193725 12147528625553744874447647)
    ·
      refine ⟨18221292938330617311671471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12147528625553744874447647 18221292938330617311671471)
      ·
        refine ⟨27331939407495925967507207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18221292938330617311671471 27331939407495925967507207)
        ·
          refine ⟨40997909111243888951260811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27331939407495925967507207 40997909111243888951260811)
          ·
            refine ⟨61496863666865833426891217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40997909111243888951260811 61496863666865833426891217)
            ·
              refine ⟨46122647750149375070168413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61496863666865833426891217 46122647750149375070168413)
              ·
                refine ⟨17295992906306015651313155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46122647750149375070168413 17295992906306015651313155)
                ·
                  refine ⟨25943989359459023476969733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17295992906306015651313155 25943989359459023476969733)
                  ·
                    refine ⟨4864498004898566901931825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25943989359459023476969733 4864498004898566901931825)
                    ·
                      refine ⟨3648373503673925176448869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4864498004898566901931825 3648373503673925176448869)
                      ·
                        rfl

theorem cell23_7105182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 3, 1, 4, 2].length) (baseStart_7105182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7105182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7105182 prefixEnd_7105182 := by exact prefixLift 7105182
  have htrace : WordTrace (prefixWord ++ tailWord_7105182) baseStart_7105182 baseEnd_7105182 := by
    simpa [prefixWord, tailWord_7105182, baseEnd_7105182] using wordTrace_append hprefix tailTrace_7105182
  have hstable : (prefixWord ++ tailWord_7105182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7105182).length < 2 ^ (prefixWord ++ tailWord_7105182).sum := by decide
  have hdescent : baseEnd_7105182 < baseStart_7105182 := by decide
  rcases family_descends (prefixWord ++ tailWord_7105182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7105221 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 2, 2, 8]
def baseStart_7105221 : Nat := 118140960795 + 7105221 * 2 ^ 59
def prefixEnd_7105221 : Nat := 4983230072969 + 3 ^ 40 * 7105221 * 2
def baseEnd_7105221 : Nat := 3648393529419450523861189

theorem tailTrace_7105221 : CollatzResearch.WordTrace tailWord_7105221 prefixEnd_7105221 3648393529419450523861189 := by
  unfold tailWord_7105221
  simp only [CollatzResearch.WordTrace]
  refine ⟨259148699792005266982219517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172765799861336844654813011 259148699792005266982219517)
  ·
    refine ⟨97180762422001975118332319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259148699792005266982219517 97180762422001975118332319)
    ·
      refine ⟨145771143633002962677498479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97180762422001975118332319 145771143633002962677498479)
      ·
        refine ⟨218656715449504444016247719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145771143633002962677498479 218656715449504444016247719)
        ·
          refine ⟨327985073174256666024371579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218656715449504444016247719 327985073174256666024371579)
          ·
            refine ⟨491977609761384999036557369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327985073174256666024371579 491977609761384999036557369)
            ·
              refine ⟨368983207321038749277418027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 491977609761384999036557369 368983207321038749277418027)
              ·
                refine ⟨553474810981558123916127041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 368983207321038749277418027 553474810981558123916127041)
                ·
                  refine ⟨415106108236168592937095281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 553474810981558123916127041 415106108236168592937095281)
                  ·
                    refine ⟨311329581177126444702821461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 415106108236168592937095281 311329581177126444702821461)
                    ·
                      refine ⟨3648393529419450523861189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 311329581177126444702821461 3648393529419450523861189)
                      ·
                        rfl

theorem cell23_7105221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 2, 8].length) (baseStart_7105221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7105221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7105221 prefixEnd_7105221 := by exact prefixLift 7105221
  have htrace : WordTrace (prefixWord ++ tailWord_7105221) baseStart_7105221 baseEnd_7105221 := by
    simpa [prefixWord, tailWord_7105221, baseEnd_7105221] using wordTrace_append hprefix tailTrace_7105221
  have hstable : (prefixWord ++ tailWord_7105221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7105221).length < 2 ^ (prefixWord ++ tailWord_7105221).sum := by decide
  have hdescent : baseEnd_7105221 < baseStart_7105221 := by decide
  rcases family_descends (prefixWord ++ tailWord_7105221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7105231 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 4, 8]
def baseStart_7105231 : Nat := 118140960795 + 7105231 * 2 ^ 59
def prefixEnd_7105231 : Nat := 4983230072969 + 3 ^ 40 * 7105231 * 2
def baseEnd_7105231 : Nat := 1216132888075331828245381

theorem tailTrace_7105231 : CollatzResearch.WordTrace tailWord_7105231 prefixEnd_7105231 1216132888075331828245381 := by
  unfold tailWord_7105231
  simp only [CollatzResearch.WordTrace]
  refine ⟨259149064521969038690083547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172766043014646025793389031 259149064521969038690083547)
  ·
    refine ⟨388723596782953558035125321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259149064521969038690083547 388723596782953558035125321)
    ·
      refine ⟨291542697587215168526343991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 388723596782953558035125321 291542697587215168526343991)
      ·
        refine ⟨437314046380822752789515987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291542697587215168526343991 437314046380822752789515987)
        ·
          refine ⟨655971069571234129184273981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 437314046380822752789515987 655971069571234129184273981)
          ·
            refine ⟨245989151089212798444102743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 655971069571234129184273981 245989151089212798444102743)
            ·
              refine ⟨368983726633819197666154115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245989151089212798444102743 368983726633819197666154115)
              ·
                refine ⟨553475589950728796499231173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 368983726633819197666154115 553475589950728796499231173)
                ·
                  refine ⟨103776673115761649343605845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 553475589950728796499231173 103776673115761649343605845)
                  ·
                    refine ⟨1216132888075331828245381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 103776673115761649343605845 1216132888075331828245381)
                    ·
                      rfl

theorem cell23_7105231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 8].length) (baseStart_7105231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7105231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7105231 prefixEnd_7105231 := by exact prefixLift 7105231
  have htrace : WordTrace (prefixWord ++ tailWord_7105231) baseStart_7105231 baseEnd_7105231 := by
    simpa [prefixWord, tailWord_7105231, baseEnd_7105231] using wordTrace_append hprefix tailTrace_7105231
  have hstable : (prefixWord ++ tailWord_7105231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7105231).length < 2 ^ (prefixWord ++ tailWord_7105231).sum := by decide
  have hdescent : baseEnd_7105231 < baseStart_7105231 := by decide
  rcases family_descends (prefixWord ++ tailWord_7105231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7105282 : List Nat := [3, 4, 1, 1, 1, 2, 1, 3, 3, 4]
def baseStart_7105282 : Nat := 118140960795 + 7105282 * 2 ^ 59
def prefixEnd_7105282 : Nat := 4983230072969 + 3 ^ 40 * 7105282 * 2
def baseEnd_7105282 : Nat := 1216141617246458261732803

theorem tailTrace_7105282 : CollatzResearch.WordTrace tailWord_7105282 prefixEnd_7105282 1216141617246458261732803 := by
  unfold tailWord_7105282
  simp only [CollatzResearch.WordTrace]
  refine ⟨64787731161196068600047525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172767283096522849600126733 64787731161196068600047525)
  ·
    refine ⟨12147699592724262862508911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64787731161196068600047525 12147699592724262862508911)
    ·
      refine ⟨18221549389086394293763367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12147699592724262862508911 18221549389086394293763367)
      ·
        refine ⟨27332324083629591440645051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18221549389086394293763367 27332324083629591440645051)
        ·
          refine ⟨40998486125444387160967577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27332324083629591440645051 40998486125444387160967577)
          ·
            refine ⟨30748864594083290370725683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40998486125444387160967577 30748864594083290370725683)
            ·
              refine ⟨46123296891124935556088525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30748864594083290370725683 46123296891124935556088525)
              ·
                refine ⟨17296236334171850833533197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46123296891124935556088525 17296236334171850833533197)
                ·
                  refine ⟨6486088625314444062574949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17296236334171850833533197 6486088625314444062574949)
                  ·
                    refine ⟨1216141617246458261732803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6486088625314444062574949 1216141617246458261732803)
                    ·
                      rfl

theorem cell23_7105282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_7105282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7105282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7105282 prefixEnd_7105282 := by exact prefixLift 7105282
  have htrace : WordTrace (prefixWord ++ tailWord_7105282) baseStart_7105282 baseEnd_7105282 := by
    simpa [prefixWord, tailWord_7105282, baseEnd_7105282] using wordTrace_append hprefix tailTrace_7105282
  have hstable : (prefixWord ++ tailWord_7105282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7105282).length < 2 ^ (prefixWord ++ tailWord_7105282).sum := by decide
  have hdescent : baseEnd_7105282 < baseStart_7105282 := by decide
  rcases family_descends (prefixWord ++ tailWord_7105282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7105295 : List Nat := [1, 1, 2, 1, 1, 1, 9, 1, 6]
def baseStart_7105295 : Nat := 118140960795 + 7105295 * 2 ^ 59
def prefixEnd_7105295 : Nat := 4983230072969 + 3 ^ 40 * 7105295 * 2
def baseEnd_7105295 : Nat := 405381280776431470481761

theorem tailTrace_7105295 : CollatzResearch.WordTrace tailWord_7105295 prefixEnd_7105295 405381280776431470481761 := by
  unfold tailWord_7105295
  simp only [CollatzResearch.WordTrace]
  refine ⟨259151398793737177620413339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172767599195824785080275559 259151398793737177620413339)
  ·
    refine ⟨388727098190605766430620009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259151398793737177620413339 388727098190605766430620009)
    ·
      refine ⟨291545323642954324822965007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 388727098190605766430620009 291545323642954324822965007)
      ·
        refine ⟨437317985464431487234447511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291545323642954324822965007 437317985464431487234447511)
        ·
          refine ⟨655976978196647230851671267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 437317985464431487234447511 655976978196647230851671267)
          ·
            refine ⟨983965467294970846277506901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 655976978196647230851671267 983965467294970846277506901)
            ·
              refine ⟨5765422659931469802407267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 983965467294970846277506901 5765422659931469802407267)
              ·
                refine ⟨8648133989897204703610901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5765422659931469802407267 8648133989897204703610901)
                ·
                  refine ⟨405381280776431470481761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8648133989897204703610901 405381280776431470481761)
                  ·
                    rfl

theorem cell23_7105295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 9, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 9, 1, 6].length) (baseStart_7105295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7105295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7105295 prefixEnd_7105295 := by exact prefixLift 7105295
  have htrace : WordTrace (prefixWord ++ tailWord_7105295) baseStart_7105295 baseEnd_7105295 := by
    simpa [prefixWord, tailWord_7105295, baseEnd_7105295] using wordTrace_append hprefix tailTrace_7105295
  have hstable : (prefixWord ++ tailWord_7105295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7105295).length < 2 ^ (prefixWord ++ tailWord_7105295).sum := by decide
  have hdescent : baseEnd_7105295 < baseStart_7105295 := by decide
  rcases family_descends (prefixWord ++ tailWord_7105295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7105305 : List Nat := [1, 2, 1, 2, 1, 1, 1, 5, 5, 1, 3]
def baseStart_7105305 : Nat := 118140960795 + 7105305 * 2 ^ 59
def prefixEnd_7105305 : Nat := 4983230072969 + 3 ^ 40 * 7105305 * 2
def baseEnd_7105305 : Nat := 3648436661794428195210803

theorem tailTrace_7105305 : CollatzResearch.WordTrace tailWord_7105305 prefixEnd_7105305 3648436661794428195210803 := by
  unfold tailWord_7105305
  simp only [CollatzResearch.WordTrace]
  refine ⟨259151763523700949328277369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172767842349133966218851579 259151763523700949328277369)
  ·
    refine ⟨194363822642775711996208027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259151763523700949328277369 194363822642775711996208027)
    ·
      refine ⟨291545733964163567994312041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194363822642775711996208027 291545733964163567994312041)
      ·
        refine ⟨218659300473122675995734031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291545733964163567994312041 218659300473122675995734031)
        ·
          refine ⟨327988950709684013993601047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218659300473122675995734031 327988950709684013993601047)
          ·
            refine ⟨491983426064526020990401571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327988950709684013993601047 491983426064526020990401571)
            ·
              refine ⟨737975139096789031485602357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 491983426064526020990401571 737975139096789031485602357)
              ·
                refine ⟨69185169290323971701775221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 737975139096789031485602357 69185169290323971701775221)
                ·
                  refine ⟨6486109620967872347041427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69185169290323971701775221 6486109620967872347041427)
                  ·
                    refine ⟨9729164431451808520562141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6486109620967872347041427 9729164431451808520562141)
                    ·
                      refine ⟨3648436661794428195210803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9729164431451808520562141 3648436661794428195210803)
                      ·
                        rfl

theorem cell23_7105305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 5, 1, 3].length) (baseStart_7105305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7105305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7105305 prefixEnd_7105305 := by exact prefixLift 7105305
  have htrace : WordTrace (prefixWord ++ tailWord_7105305) baseStart_7105305 baseEnd_7105305 := by
    simpa [prefixWord, tailWord_7105305, baseEnd_7105305] using wordTrace_append hprefix tailTrace_7105305
  have hstable : (prefixWord ++ tailWord_7105305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7105305).length < 2 ^ (prefixWord ++ tailWord_7105305).sum := by decide
  have hdescent : baseEnd_7105305 < baseStart_7105305 := by decide
  rcases family_descends (prefixWord ++ tailWord_7105305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7105316 : List Nat := [2, 3, 1, 3, 3, 2, 1, 3, 1, 4]
def baseStart_7105316 : Nat := 118140960795 + 7105316 * 2 ^ 59
def prefixEnd_7105316 : Nat := 4983230072969 + 3 ^ 40 * 7105316 * 2
def baseEnd_7105316 : Nat := 1216147436693875884057751

theorem tailTrace_7105316 : CollatzResearch.WordTrace tailWord_7105316 prefixEnd_7105316 1216147436693875884057751 := by
  unfold tailWord_7105316
  simp only [CollatzResearch.WordTrace]
  refine ⟨129576082363330549103463901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172768109817774065471285201 129576082363330549103463901)
  ·
    refine ⟨48591030886248955913798963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129576082363330549103463901 48591030886248955913798963)
    ·
      refine ⟨72886546329373433870698445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48591030886248955913798963 72886546329373433870698445)
      ·
        refine ⟨27332454873515037701511917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72886546329373433870698445 27332454873515037701511917)
        ·
          refine ⟨10249670577568139138066969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27332454873515037701511917 10249670577568139138066969)
          ·
            refine ⟨7687252933176104353550227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10249670577568139138066969 7687252933176104353550227)
            ·
              refine ⟨11530879399764156530325341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7687252933176104353550227 11530879399764156530325341)
              ·
                refine ⟨4324079774911558698872003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11530879399764156530325341 4324079774911558698872003)
                ·
                  refine ⟨6486119662367338048308005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4324079774911558698872003 6486119662367338048308005)
                  ·
                    refine ⟨1216147436693875884057751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6486119662367338048308005 1216147436693875884057751)
                    ·
                      rfl

theorem cell23_7105316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 3, 1, 4].length) (baseStart_7105316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7105316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7105316 prefixEnd_7105316 := by exact prefixLift 7105316
  have htrace : WordTrace (prefixWord ++ tailWord_7105316) baseStart_7105316 baseEnd_7105316 := by
    simpa [prefixWord, tailWord_7105316, baseEnd_7105316] using wordTrace_append hprefix tailTrace_7105316
  have hstable : (prefixWord ++ tailWord_7105316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7105316).length < 2 ^ (prefixWord ++ tailWord_7105316).sum := by decide
  have hdescent : baseEnd_7105316 < baseStart_7105316 := by decide
  rcases family_descends (prefixWord ++ tailWord_7105316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7105372 : List Nat := [2, 2, 4, 2, 1, 2, 1, 2, 1, 6]
def baseStart_7105372 : Nat := 118140960795 + 7105372 * 2 ^ 59
def prefixEnd_7105372 : Nat := 4983230072969 + 3 ^ 40 * 7105372 * 2
def baseEnd_7105372 : Nat := 1216157021666093144357665

theorem tailTrace_7105372 : CollatzResearch.WordTrace tailWord_7105372 prefixEnd_7105372 1216157021666093144357665 := by
  unfold tailWord_7105372
  simp only [CollatzResearch.WordTrace]
  refine ⟨129577103607229109885483185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172769471476305479847310913 129577103607229109885483185)
  ·
    refine ⟨97182827705421832414112389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129577103607229109885483185 97182827705421832414112389)
    ·
      refine ⟨18221780194766593577646073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97182827705421832414112389 18221780194766593577646073)
      ·
        refine ⟨13666335146074945183234555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18221780194766593577646073 13666335146074945183234555)
        ·
          refine ⟨20499502719112417774851833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13666335146074945183234555 20499502719112417774851833)
          ·
            refine ⟨15374627039334313331138875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20499502719112417774851833 15374627039334313331138875)
            ·
              refine ⟨23061940559001469996708313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15374627039334313331138875 23061940559001469996708313)
              ·
                refine ⟨17296455419251102497531235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23061940559001469996708313 17296455419251102497531235)
                ·
                  refine ⟨25944683128876653746296853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17296455419251102497531235 25944683128876653746296853)
                  ·
                    refine ⟨1216157021666093144357665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25944683128876653746296853 1216157021666093144357665)
                    ·
                      rfl

theorem cell23_7105372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_7105372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7105372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7105372 prefixEnd_7105372 := by exact prefixLift 7105372
  have htrace : WordTrace (prefixWord ++ tailWord_7105372) baseStart_7105372 baseEnd_7105372 := by
    simpa [prefixWord, tailWord_7105372, baseEnd_7105372] using wordTrace_append hprefix tailTrace_7105372
  have hstable : (prefixWord ++ tailWord_7105372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7105372).length < 2 ^ (prefixWord ++ tailWord_7105372).sum := by decide
  have hdescent : baseEnd_7105372 < baseStart_7105372 := by decide
  rcases family_descends (prefixWord ++ tailWord_7105372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7105375 : List Nat := [1, 1, 2, 3, 1, 3, 3, 2, 1, 2, 4]
def baseStart_7105375 : Nat := 118140960795 + 7105375 * 2 ^ 59
def prefixEnd_7105375 : Nat := 4983230072969 + 3 ^ 40 * 7105375 * 2
def baseEnd_7105375 : Nat := 3648472605440242921335481

theorem tailTrace_7105375 : CollatzResearch.WordTrace tailWord_7105375 prefixEnd_7105375 3648472605440242921335481 := by
  unfold tailWord_7105375
  simp only [CollatzResearch.WordTrace]
  refine ⟨259154316633447351283325579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172769544422298234188883719 259154316633447351283325579)
  ·
    refine ⟨388731474950171026924988369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259154316633447351283325579 388731474950171026924988369)
    ·
      refine ⟨291548606212628270193741277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 388731474950171026924988369 291548606212628270193741277)
      ·
        refine ⟨109330727329735601322652979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 291548606212628270193741277 109330727329735601322652979)
        ·
          refine ⟨163996090994603401983979469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109330727329735601322652979 163996090994603401983979469)
          ·
            refine ⟨61498534122976275743992301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163996090994603401983979469 61498534122976275743992301)
            ·
              refine ⟨23061950296116103403997113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61498534122976275743992301 23061950296116103403997113)
              ·
                refine ⟨17296462722087077552997835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23061950296116103403997113 17296462722087077552997835)
                ·
                  refine ⟨25944694083130616329496753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17296462722087077552997835 25944694083130616329496753)
                  ·
                    refine ⟨19458520562347962247122565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25944694083130616329496753 19458520562347962247122565)
                    ·
                      refine ⟨3648472605440242921335481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19458520562347962247122565 3648472605440242921335481)
                      ·
                        rfl

theorem cell23_7105375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 2, 1, 2, 4].length) (baseStart_7105375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7105375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7105375 prefixEnd_7105375 := by exact prefixLift 7105375
  have htrace : WordTrace (prefixWord ++ tailWord_7105375) baseStart_7105375 baseEnd_7105375 := by
    simpa [prefixWord, tailWord_7105375, baseEnd_7105375] using wordTrace_append hprefix tailTrace_7105375
  have hstable : (prefixWord ++ tailWord_7105375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7105375).length < 2 ^ (prefixWord ++ tailWord_7105375).sum := by decide
  have hdescent : baseEnd_7105375 < baseStart_7105375 := by decide
  rcases family_descends (prefixWord ++ tailWord_7105375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7105379 : List Nat := [1, 1, 1, 5, 3, 2, 3, 1, 1, 1, 4]
def baseStart_7105379 : Nat := 118140960795 + 7105379 * 2 ^ 59
def prefixEnd_7105379 : Nat := 4983230072969 + 3 ^ 40 * 7105379 * 2
def baseEnd_7105379 : Nat := 3648474659362860905685463

theorem tailTrace_7105379 : CollatzResearch.WordTrace tailWord_7105379 prefixEnd_7105379 3648474659362860905685463 := by
  unfold tailWord_7105379
  simp only [CollatzResearch.WordTrace]
  refine ⟨259154462525432859966471191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172769641683621906644314127 259154462525432859966471191)
  ·
    refine ⟨388731693788149289949706787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259154462525432859966471191 388731693788149289949706787)
    ·
      refine ⟨583097540682223934924560181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388731693788149289949706787 583097540682223934924560181)
      ·
        refine ⟨54665394438958493899177517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 583097540682223934924560181 54665394438958493899177517)
        ·
          refine ⟨20499522914609435212191569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54665394438958493899177517 20499522914609435212191569)
          ·
            refine ⟨15374642185957076409143677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20499522914609435212191569 15374642185957076409143677)
            ·
              refine ⟨5765490819733903653428879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15374642185957076409143677 5765490819733903653428879)
              ·
                refine ⟨8648236229600855480143319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5765490819733903653428879 8648236229600855480143319)
                ·
                  refine ⟨12972354344401283220214979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8648236229600855480143319 12972354344401283220214979)
                  ·
                    refine ⟨19458531516601924830322469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12972354344401283220214979 19458531516601924830322469)
                    ·
                      refine ⟨3648474659362860905685463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19458531516601924830322469 3648474659362860905685463)
                      ·
                        rfl

theorem cell23_7105379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 3, 1, 1, 1, 4].length) (baseStart_7105379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7105379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7105379 prefixEnd_7105379 := by exact prefixLift 7105379
  have htrace : WordTrace (prefixWord ++ tailWord_7105379) baseStart_7105379 baseEnd_7105379 := by
    simpa [prefixWord, tailWord_7105379, baseEnd_7105379] using wordTrace_append hprefix tailTrace_7105379
  have hstable : (prefixWord ++ tailWord_7105379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7105379).length < 2 ^ (prefixWord ++ tailWord_7105379).sum := by decide
  have hdescent : baseEnd_7105379 < baseStart_7105379 := by decide
  rcases family_descends (prefixWord ++ tailWord_7105379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7105390 : List Nat := [4, 1, 2, 3, 2, 2, 2, 2, 1, 1, 3]
def baseStart_7105390 : Nat := 118140960795 + 7105390 * 2 ^ 59
def prefixEnd_7105390 : Nat := 4983230072969 + 3 ^ 40 * 7105390 * 2
def baseEnd_7105390 : Nat := 3648480307650060362647913

theorem tailTrace_7105390 : CollatzResearch.WordTrace tailWord_7105390 prefixEnd_7105390 3648480307650060362647913 := by
  unfold tailWord_7105390
  simp only [CollatzResearch.WordTrace]
  refine ⟨32394357966049126105640203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172769909152262005896747749 32394357966049126105640203)
  ·
    refine ⟨48591536949073689158460305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32394357966049126105640203 48591536949073689158460305)
    ·
      refine ⟨36443652711805266868845229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48591536949073689158460305 36443652711805266868845229)
      ·
        refine ⟨13666369766926975075816961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36443652711805266868845229 13666369766926975075816961)
        ·
          refine ⟨10249777325195231306862721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13666369766926975075816961 10249777325195231306862721)
          ·
            refine ⟨7687332993896423480147041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10249777325195231306862721 7687332993896423480147041)
            ·
              refine ⟨5765499745422317610110281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7687332993896423480147041 5765499745422317610110281)
              ·
                refine ⟨4324124809066738207582711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5765499745422317610110281 4324124809066738207582711)
                ·
                  refine ⟨6486187213600107311374067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4324124809066738207582711 6486187213600107311374067)
                  ·
                    refine ⟨9729280820400160967061101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6486187213600107311374067 9729280820400160967061101)
                    ·
                      refine ⟨3648480307650060362647913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9729280820400160967061101 3648480307650060362647913)
                      ·
                        rfl

theorem cell23_7105390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_7105390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7105390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7105390 prefixEnd_7105390 := by exact prefixLift 7105390
  have htrace : WordTrace (prefixWord ++ tailWord_7105390) baseStart_7105390 baseEnd_7105390 := by
    simpa [prefixWord, tailWord_7105390, baseEnd_7105390] using wordTrace_append hprefix tailTrace_7105390
  have hstable : (prefixWord ++ tailWord_7105390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7105390).length < 2 ^ (prefixWord ++ tailWord_7105390).sum := by decide
  have hdescent : baseEnd_7105390 < baseStart_7105390 := by decide
  rcases family_descends (prefixWord ++ tailWord_7105390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7105412 : List Nat := [2, 3, 2, 1, 1, 1, 1, 2, 6, 1, 3]
def baseStart_7105412 : Nat := 118140960795 + 7105412 * 2 ^ 59
def prefixEnd_7105412 : Nat := 4983230072969 + 3 ^ 40 * 7105412 * 2
def baseEnd_7105412 : Nat := 3648491604224459276572811

theorem tailTrace_7105412 : CollatzResearch.WordTrace tailWord_7105412 prefixEnd_7105412 3648491604224459276572811 := by
  unfold tailWord_7105412
  simp only [CollatzResearch.WordTrace]
  refine ⟨129577833067156653301211245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172770444089542204401614993 129577833067156653301211245)
  ·
    refine ⟨48591687400183744987954217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129577833067156653301211245 48591687400183744987954217)
    ·
      refine ⟨36443765550137808740965663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48591687400183744987954217 36443765550137808740965663)
      ·
        refine ⟨54665648325206713111448495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36443765550137808740965663 54665648325206713111448495)
        ·
          refine ⟨81998472487810069667172743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54665648325206713111448495 81998472487810069667172743)
          ·
            refine ⟨122997708731715104500759115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81998472487810069667172743 122997708731715104500759115)
            ·
              refine ⟨184496563097572656751138673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122997708731715104500759115 184496563097572656751138673)
              ·
                refine ⟨138372422323179492563354005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184496563097572656751138673 138372422323179492563354005)
                ·
                  refine ⟨6486207296399038713907219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 138372422323179492563354005 6486207296399038713907219)
                  ·
                    refine ⟨9729310944598558070860829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6486207296399038713907219 9729310944598558070860829)
                    ·
                      refine ⟨3648491604224459276572811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9729310944598558070860829 3648491604224459276572811)
                      ·
                        rfl

theorem cell23_7105412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 6, 1, 3].length) (baseStart_7105412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7105412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7105412 prefixEnd_7105412 := by exact prefixLift 7105412
  have htrace : WordTrace (prefixWord ++ tailWord_7105412) baseStart_7105412 baseEnd_7105412 := by
    simpa [prefixWord, tailWord_7105412, baseEnd_7105412] using wordTrace_append hprefix tailTrace_7105412
  have hstable : (prefixWord ++ tailWord_7105412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7105412).length < 2 ^ (prefixWord ++ tailWord_7105412).sum := by decide
  have hdescent : baseEnd_7105412 < baseStart_7105412 := by decide
  rcases family_descends (prefixWord ++ tailWord_7105412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7105430 : List Nat := [5, 3, 1, 1, 1, 3, 2, 1, 1, 1, 4]
def baseStart_7105430 : Nat := 118140960795 + 7105430 * 2 ^ 59
def prefixEnd_7105430 : Nat := 4983230072969 + 3 ^ 40 * 7105430 * 2
def baseEnd_7105430 : Nat := 3648500846876240206147729

theorem tailTrace_7105430 : CollatzResearch.WordTrace tailWord_7105430 prefixEnd_7105430 3648500846876240206147729 := by
  unfold tailWord_7105430
  simp only [CollatzResearch.WordTrace]
  refine ⟨16197270165515505979786109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 172770881765498730451051829 16197270165515505979786109)
  ·
    refine ⟨6073976312068314742419791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16197270165515505979786109 6073976312068314742419791)
    ·
      refine ⟨9110964468102472113629687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6073976312068314742419791 9110964468102472113629687)
      ·
        refine ⟨13666446702153708170444531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9110964468102472113629687 13666446702153708170444531)
        ·
          refine ⟨20499670053230562255666797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13666446702153708170444531 20499670053230562255666797)
          ·
            refine ⟨7687376269961460845875049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20499670053230562255666797 7687376269961460845875049)
            ·
              refine ⟨5765532202471095634406287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7687376269961460845875049 5765532202471095634406287)
              ·
                refine ⟨8648298303706643451609431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5765532202471095634406287 8648298303706643451609431)
                ·
                  refine ⟨12972447455559965177414147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8648298303706643451609431 12972447455559965177414147)
                  ·
                    refine ⟨19458671183339947766121221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12972447455559965177414147 19458671183339947766121221)
                    ·
                      refine ⟨3648500846876240206147729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19458671183339947766121221 3648500846876240206147729)
                      ·
                        rfl

theorem cell23_7105430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_7105430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7105430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7105430 prefixEnd_7105430 := by exact prefixLift 7105430
  have htrace : WordTrace (prefixWord ++ tailWord_7105430) baseStart_7105430 baseEnd_7105430 := by
    simpa [prefixWord, tailWord_7105430, baseEnd_7105430] using wordTrace_append hprefix tailTrace_7105430
  have hstable : (prefixWord ++ tailWord_7105430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7105430).length < 2 ^ (prefixWord ++ tailWord_7105430).sum := by decide
  have hdescent : baseEnd_7105430 < baseStart_7105430 := by decide
  rcases family_descends (prefixWord ++ tailWord_7105430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7105455 : List Nat := [1, 1, 2, 1, 2, 2, 2, 3, 2, 4, 3]
def baseStart_7105455 : Nat := 118140960795 + 7105455 * 2 ^ 59
def prefixEnd_7105455 : Nat := 4983230072969 + 3 ^ 40 * 7105455 * 2
def baseEnd_7105455 : Nat := 3648513683892602608335113

theorem tailTrace_7105455 : CollatzResearch.WordTrace tailWord_7105455 prefixEnd_7105455 3648513683892602608335113 := by
  unfold tailWord_7105455
  simp only [CollatzResearch.WordTrace]
  refine ⟨259157234473157524946237819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172771489648771683297491879 259157234473157524946237819)
  ·
    refine ⟨388735851709736287419356729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259157234473157524946237819 388735851709736287419356729)
    ·
      refine ⟨291551888782302215564517547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 388735851709736287419356729 291551888782302215564517547)
      ·
        refine ⟨437327833173453323346776321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291551888782302215564517547 437327833173453323346776321)
        ·
          refine ⟨327995874880089992510082241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 437327833173453323346776321 327995874880089992510082241)
          ·
            refine ⟨245996906160067494382561681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 327995874880089992510082241 245996906160067494382561681)
            ·
              refine ⟨184497679620050620786921261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 245996906160067494382561681 184497679620050620786921261)
              ·
                refine ⟨69186629857518982795095473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 184497679620050620786921261 69186629857518982795095473)
                ·
                  refine ⟨51889972393139237096321605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69186629857518982795095473 51889972393139237096321605)
                  ·
                    refine ⟨9729369823713606955560301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51889972393139237096321605 9729369823713606955560301)
                    ·
                      refine ⟨3648513683892602608335113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9729369823713606955560301 3648513683892602608335113)
                      ·
                        rfl

theorem cell23_7105455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 4, 3].length) (baseStart_7105455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7105455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7105455 prefixEnd_7105455 := by exact prefixLift 7105455
  have htrace : WordTrace (prefixWord ++ tailWord_7105455) baseStart_7105455 baseEnd_7105455 := by
    simpa [prefixWord, tailWord_7105455, baseEnd_7105455] using wordTrace_append hprefix tailTrace_7105455
  have hstable : (prefixWord ++ tailWord_7105455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7105455).length < 2 ^ (prefixWord ++ tailWord_7105455).sum := by decide
  have hdescent : baseEnd_7105455 < baseStart_7105455 := by decide
  rcases family_descends (prefixWord ++ tailWord_7105455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7105524 : List Nat := [2, 6, 2, 1, 1, 2, 1, 2, 1, 3, 2]
def baseStart_7105524 : Nat := 118140960795 + 7105524 * 2 ^ 59
def prefixEnd_7105524 : Nat := 4983230072969 + 3 ^ 40 * 7105524 * 2
def baseEnd_7105524 : Nat := 3648549114057762838372297

theorem tailTrace_7105524 : CollatzResearch.WordTrace tailWord_7105524 prefixEnd_7105524 3648549114057762838372297 := by
  unfold tailWord_7105524
  simp only [CollatzResearch.WordTrace]
  refine ⟨129579875554953774865249813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172773167406605033153666417 129579875554953774865249813)
  ·
    refine ⟨6074056666638458196808585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 129579875554953774865249813 6074056666638458196808585)
    ·
      refine ⟨4555542499978843647606439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6074056666638458196808585 4555542499978843647606439)
      ·
        refine ⟨6833313749968265471409659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4555542499978843647606439 6833313749968265471409659)
        ·
          refine ⟨10249970624952398207114489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6833313749968265471409659 10249970624952398207114489)
          ·
            refine ⟨7687477968714298655335867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10249970624952398207114489 7687477968714298655335867)
            ·
              refine ⟨11531216953071447983003801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7687477968714298655335867 11531216953071447983003801)
              ·
                refine ⟨8648412714803585987252851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11531216953071447983003801 8648412714803585987252851)
                ·
                  refine ⟨12972619072205378980879277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8648412714803585987252851 12972619072205378980879277)
                  ·
                    refine ⟨4864732152077017117829729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12972619072205378980879277 4864732152077017117829729)
                    ·
                      refine ⟨3648549114057762838372297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4864732152077017117829729 3648549114057762838372297)
                      ·
                        rfl

theorem cell23_7105524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_7105524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7105524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7105524 prefixEnd_7105524 := by exact prefixLift 7105524
  have htrace : WordTrace (prefixWord ++ tailWord_7105524) baseStart_7105524 baseEnd_7105524 := by
    simpa [prefixWord, tailWord_7105524, baseEnd_7105524] using wordTrace_append hprefix tailTrace_7105524
  have hstable : (prefixWord ++ tailWord_7105524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7105524).length < 2 ^ (prefixWord ++ tailWord_7105524).sum := by decide
  have hdescent : baseEnd_7105524 < baseStart_7105524 := by decide
  rcases family_descends (prefixWord ++ tailWord_7105524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7105555 : List Nat := [1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 6]
def baseStart_7105555 : Nat := 118140960795 + 7105555 * 2 ^ 59
def prefixEnd_7105555 : Nat := 4983230072969 + 3 ^ 40 * 7105555 * 2
def baseEnd_7105555 : Nat := 3648565031958052217084653

theorem tailTrace_7105555 : CollatzResearch.WordTrace tailWord_7105555 prefixEnd_7105555 3648565031958052217084653 := by
  unfold tailWord_7105555
  simp only [CollatzResearch.WordTrace]
  refine ⟨259160881772795242024878119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172773921181863494683252079 259160881772795242024878119)
  ·
    refine ⟨388741322659192863037317179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259160881772795242024878119 388741322659192863037317179)
    ·
      refine ⟨583111983988789294555975769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388741322659192863037317179 583111983988789294555975769)
      ·
        refine ⟨437333987991591970916981827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 583111983988789294555975769 437333987991591970916981827)
        ·
          refine ⟨656000981987387956375472741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 437333987991591970916981827 656000981987387956375472741)
          ·
            refine ⟨123000184122635241820401139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 656000981987387956375472741 123000184122635241820401139)
            ·
              refine ⟨184500276183952862730601709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123000184122635241820401139 184500276183952862730601709)
              ·
                refine ⟨69187603568982323523975641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 184500276183952862730601709 69187603568982323523975641)
                ·
                  refine ⟨51890702676736742642981731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69187603568982323523975641 51890702676736742642981731)
                  ·
                    refine ⟨77836054015105113964472597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51890702676736742642981731 77836054015105113964472597)
                    ·
                      refine ⟨3648565031958052217084653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77836054015105113964472597 3648565031958052217084653)
                      ·
                        rfl

theorem cell23_7105555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 6].length) (baseStart_7105555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7105555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7105555 prefixEnd_7105555 := by exact prefixLift 7105555
  have htrace : WordTrace (prefixWord ++ tailWord_7105555) baseStart_7105555 baseEnd_7105555 := by
    simpa [prefixWord, tailWord_7105555, baseEnd_7105555] using wordTrace_append hprefix tailTrace_7105555
  have hstable : (prefixWord ++ tailWord_7105555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7105555).length < 2 ^ (prefixWord ++ tailWord_7105555).sum := by decide
  have hdescent : baseEnd_7105555 < baseStart_7105555 := by decide
  rcases family_descends (prefixWord ++ tailWord_7105555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7105559 : List Nat := [1, 1, 3, 5, 1, 1, 2, 2, 2, 1, 4]
def baseStart_7105559 : Nat := 118140960795 + 7105559 * 2 ^ 59
def prefixEnd_7105559 : Nat := 4983230072969 + 3 ^ 40 * 7105559 * 2
def baseEnd_7105559 : Nat := 3648567085880670201434635

theorem tailTrace_7105559 : CollatzResearch.WordTrace tailWord_7105559 prefixEnd_7105559 3648567085880670201434635 := by
  unfold tailWord_7105559
  simp only [CollatzResearch.WordTrace]
  refine ⟨259161027664780750708023731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172774018443187167138682487 259161027664780750708023731)
  ·
    refine ⟨388741541497171126062035597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259161027664780750708023731 388741541497171126062035597)
    ·
      refine ⟨145778078061439172273263349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 388741541497171126062035597 145778078061439172273263349)
      ·
        refine ⟨13666694818259922400618439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 145778078061439172273263349 13666694818259922400618439)
        ·
          refine ⟨20500042227389883600927659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13666694818259922400618439 20500042227389883600927659)
          ·
            refine ⟨30750063341084825401391489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20500042227389883600927659 30750063341084825401391489)
            ·
              refine ⟨23062547505813619051043617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30750063341084825401391489 23062547505813619051043617)
              ·
                refine ⟨17296910629360214288282713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23062547505813619051043617 17296910629360214288282713)
                ·
                  refine ⟨12972682972020160716212035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17296910629360214288282713 12972682972020160716212035)
                  ·
                    refine ⟨19459024458030241074318053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12972682972020160716212035 19459024458030241074318053)
                    ·
                      refine ⟨3648567085880670201434635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19459024458030241074318053 3648567085880670201434635)
                      ·
                        rfl

theorem cell23_7105559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_7105559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7105559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7105559 prefixEnd_7105559 := by exact prefixLift 7105559
  have htrace : WordTrace (prefixWord ++ tailWord_7105559) baseStart_7105559 baseEnd_7105559 := by
    simpa [prefixWord, tailWord_7105559, baseEnd_7105559] using wordTrace_append hprefix tailTrace_7105559
  have hstable : (prefixWord ++ tailWord_7105559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7105559).length < 2 ^ (prefixWord ++ tailWord_7105559).sum := by decide
  have hdescent : baseEnd_7105559 < baseStart_7105559 := by decide
  rcases family_descends (prefixWord ++ tailWord_7105559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7105596 : List Nat := [2, 2, 2, 2, 2, 4, 1, 1, 2, 2, 3]
def baseStart_7105596 : Nat := 118140960795 + 7105596 * 2 ^ 59
def prefixEnd_7105596 : Nat := 4983230072969 + 3 ^ 40 * 7105596 * 2
def baseEnd_7105596 : Nat := 3648586084664886556671965

theorem tailTrace_7105596 : CollatzResearch.WordTrace tailWord_7105596 prefixEnd_7105596 3648586084664886556671965 := by
  unfold tailWord_7105596
  simp only [CollatzResearch.WordTrace]
  refine ⟨129581188582823353013560321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172774918110431137351413761 129581188582823353013560321)
  ·
    refine ⟨97185891437117514760170241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129581188582823353013560321 97185891437117514760170241)
    ·
      refine ⟨72889418577838136070127681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97185891437117514760170241 72889418577838136070127681)
      ·
        refine ⟨54667063933378602052595761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72889418577838136070127681 54667063933378602052595761)
        ·
          refine ⟨41000297950033951539446821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54667063933378602052595761 41000297950033951539446821)
          ·
            refine ⟨7687555865631365913646279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41000297950033951539446821 7687555865631365913646279)
            ·
              refine ⟨11531333798447048870469419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7687555865631365913646279 11531333798447048870469419)
              ·
                refine ⟨17297000697670573305704129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11531333798447048870469419 17297000697670573305704129)
                ·
                  refine ⟨12972750523252929979278097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17297000697670573305704129 12972750523252929979278097)
                  ·
                    refine ⟨9729562892439697484458573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12972750523252929979278097 9729562892439697484458573)
                    ·
                      refine ⟨3648586084664886556671965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9729562892439697484458573 3648586084664886556671965)
                      ·
                        rfl

theorem cell23_7105596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 1, 2, 2, 3].length) (baseStart_7105596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7105596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7105596 prefixEnd_7105596 := by exact prefixLift 7105596
  have htrace : WordTrace (prefixWord ++ tailWord_7105596) baseStart_7105596 baseEnd_7105596 := by
    simpa [prefixWord, tailWord_7105596, baseEnd_7105596] using wordTrace_append hprefix tailTrace_7105596
  have hstable : (prefixWord ++ tailWord_7105596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7105596).length < 2 ^ (prefixWord ++ tailWord_7105596).sum := by decide
  have hdescent : baseEnd_7105596 < baseStart_7105596 := by decide
  rcases family_descends (prefixWord ++ tailWord_7105596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7105646 : List Nat := [4, 1, 2, 2, 1, 3, 2, 2, 1, 5]
def baseStart_7105646 : Nat := 118140960795 + 7105646 * 2 ^ 59
def prefixEnd_7105646 : Nat := 4983230072969 + 3 ^ 40 * 7105646 * 2
def baseEnd_7105646 : Nat := 1216203919565870453682245

theorem tailTrace_7105646 : CollatzResearch.WordTrace tailWord_7105646 prefixEnd_7105646 1216203919565870453682245 := by
  unfold tailWord_7105646
  simp only [CollatzResearch.WordTrace]
  refine ⟨32395525101933195570805099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172776133876977043044293861 32395525101933195570805099)
  ·
    refine ⟨48593287652899793356207649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32395525101933195570805099 48593287652899793356207649)
    ·
      refine ⟨36444965739674845017155737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48593287652899793356207649 36444965739674845017155737)
      ·
        refine ⟨27333724304756133762866803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36444965739674845017155737 27333724304756133762866803)
        ·
          refine ⟨41000586457134200644300205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27333724304756133762866803 41000586457134200644300205)
          ·
            refine ⟨15375219921425325241612577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41000586457134200644300205 15375219921425325241612577)
            ·
              refine ⟨11531414941068993931209433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15375219921425325241612577 11531414941068993931209433)
              ·
                refine ⟨8648561205801745448407075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11531414941068993931209433 8648561205801745448407075)
                ·
                  refine ⟨12972841808702618172610613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8648561205801745448407075 12972841808702618172610613)
                  ·
                    refine ⟨1216203919565870453682245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12972841808702618172610613 1216203919565870453682245)
                    ·
                      rfl

theorem cell23_7105646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 2, 1, 5].length) (baseStart_7105646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7105646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7105646 prefixEnd_7105646 := by exact prefixLift 7105646
  have htrace : WordTrace (prefixWord ++ tailWord_7105646) baseStart_7105646 baseEnd_7105646 := by
    simpa [prefixWord, tailWord_7105646, baseEnd_7105646] using wordTrace_append hprefix tailTrace_7105646
  have hstable : (prefixWord ++ tailWord_7105646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7105646).length < 2 ^ (prefixWord ++ tailWord_7105646).sum := by decide
  have hdescent : baseEnd_7105646 < baseStart_7105646 := by decide
  rcases family_descends (prefixWord ++ tailWord_7105646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7105683 : List Nat := [1, 1, 1, 2, 1, 2, 4, 6, 1, 2, 2]
def baseStart_7105683 : Nat := 118140960795 + 7105683 * 2 ^ 59
def prefixEnd_7105683 : Nat := 4983230072969 + 3 ^ 40 * 7105683 * 2
def baseEnd_7105683 : Nat := 3648630757481827716284065

theorem tailTrace_7105683 : CollatzResearch.WordTrace tailWord_7105683 prefixEnd_7105683 3648630757481827716284065 := by
  unfold tailWord_7105683
  simp only [CollatzResearch.WordTrace]
  refine ⟨259165550316331519885537703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172777033544221013257025135 259165550316331519885537703)
  ·
    refine ⟨388748325474497279828306555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259165550316331519885537703 388748325474497279828306555)
    ·
      refine ⟨583122488211745919742459833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388748325474497279828306555 583122488211745919742459833)
      ·
        refine ⟨437341866158809439806844875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 583122488211745919742459833 437341866158809439806844875)
        ·
          refine ⟨656012799238214159710267313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 437341866158809439806844875 656012799238214159710267313)
          ·
            refine ⟨492009599428660619782700485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 656012799238214159710267313 492009599428660619782700485)
            ·
              refine ⟨92251799892873866209256341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 492009599428660619782700485 92251799892873866209256341)
              ·
                refine ⟨4324303119978462478558891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 92251799892873866209256341 4324303119978462478558891)
                ·
                  refine ⟨6486454679967693717838337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4324303119978462478558891 6486454679967693717838337)
                  ·
                    refine ⟨4864841009975770288378753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6486454679967693717838337 4864841009975770288378753)
                    ·
                      refine ⟨3648630757481827716284065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4864841009975770288378753 3648630757481827716284065)
                      ·
                        rfl

theorem cell23_7105683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 6, 1, 2, 2].length) (baseStart_7105683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7105683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7105683 prefixEnd_7105683 := by exact prefixLift 7105683
  have htrace : WordTrace (prefixWord ++ tailWord_7105683) baseStart_7105683 baseEnd_7105683 := by
    simpa [prefixWord, tailWord_7105683, baseEnd_7105683] using wordTrace_append hprefix tailTrace_7105683
  have hstable : (prefixWord ++ tailWord_7105683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7105683).length < 2 ^ (prefixWord ++ tailWord_7105683).sum := by decide
  have hdescent : baseEnd_7105683 < baseStart_7105683 := by decide
  rcases family_descends (prefixWord ++ tailWord_7105683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7105703 : List Nat := [1, 1, 6, 2, 1, 1, 3, 2, 1, 2, 3]
def baseStart_7105703 : Nat := 118140960795 + 7105703 * 2 ^ 59
def prefixEnd_7105703 : Nat := 4983230072969 + 3 ^ 40 * 7105703 * 2
def baseEnd_7105703 : Nat := 3648641027094917638033973

theorem tailTrace_7105703 : CollatzResearch.WordTrace tailWord_7105703 prefixEnd_7105703 3648641027094917638033973 := by
  unfold tailWord_7105703
  simp only [CollatzResearch.WordTrace]
  refine ⟨259166279776259063301265763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172777519850839375534177175 259166279776259063301265763)
  ·
    refine ⟨388749419664388594951898645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259166279776259063301265763 388749419664388594951898645)
    ·
      refine ⟨18222629046768215388370249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 388749419664388594951898645 18222629046768215388370249)
      ·
        refine ⟨13666971785076161541277687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18222629046768215388370249 13666971785076161541277687)
        ·
          refine ⟨20500457677614242311916531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13666971785076161541277687 20500457677614242311916531)
          ·
            refine ⟨30750686516421363467874797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20500457677614242311916531 30750686516421363467874797)
            ·
              refine ⟨11531507443658011300453049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30750686516421363467874797 11531507443658011300453049)
              ·
                refine ⟨8648630582743508475339787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11531507443658011300453049 8648630582743508475339787)
                ·
                  refine ⟨12972945874115262713009681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8648630582743508475339787 12972945874115262713009681)
                  ·
                    refine ⟨9729709405586447034757261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12972945874115262713009681 9729709405586447034757261)
                    ·
                      refine ⟨3648641027094917638033973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9729709405586447034757261 3648641027094917638033973)
                      ·
                        rfl

theorem cell23_7105703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_7105703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7105703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7105703 prefixEnd_7105703 := by exact prefixLift 7105703
  have htrace : WordTrace (prefixWord ++ tailWord_7105703) baseStart_7105703 baseEnd_7105703 := by
    simpa [prefixWord, tailWord_7105703, baseEnd_7105703] using wordTrace_append hprefix tailTrace_7105703
  have hstable : (prefixWord ++ tailWord_7105703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7105703).length < 2 ^ (prefixWord ++ tailWord_7105703).sum := by decide
  have hdescent : baseEnd_7105703 < baseStart_7105703 := by decide
  rcases family_descends (prefixWord ++ tailWord_7105703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7105749 : List Nat := [1, 3, 2, 4, 1, 1, 1, 1, 1, 8]
def baseStart_7105749 : Nat := 118140960795 + 7105749 * 2 ^ 59
def prefixEnd_7105749 : Nat := 4983230072969 + 3 ^ 40 * 7105749 * 2
def baseEnd_7105749 : Nat := 1216221549068341486019587

theorem tailTrace_7105749 : CollatzResearch.WordTrace tailWord_7105749 prefixEnd_7105749 1216221549068341486019587 := by
  unfold tailWord_7105749
  simp only [CollatzResearch.WordTrace]
  refine ⟨259167957534092413157440301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172778638356061608771626867 259167957534092413157440301)
  ·
    refine ⟨97187984075284654934040113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259167957534092413157440301 97187984075284654934040113)
    ·
      refine ⟨72890988056463491200530085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97187984075284654934040113 72890988056463491200530085)
      ·
        refine ⟨13667060260586904600099391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72890988056463491200530085 13667060260586904600099391)
        ·
          refine ⟨20500590390880356900149087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13667060260586904600099391 20500590390880356900149087)
          ·
            refine ⟨30750885586320535350223631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20500590390880356900149087 30750885586320535350223631)
            ·
              refine ⟨46126328379480803025335447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30750885586320535350223631 46126328379480803025335447)
              ·
                refine ⟨69189492569221204538003171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46126328379480803025335447 69189492569221204538003171)
                ·
                  refine ⟨103784238853831806807004757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69189492569221204538003171 103784238853831806807004757)
                  ·
                    refine ⟨1216221549068341486019587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 103784238853831806807004757 1216221549068341486019587)
                    ·
                      rfl

theorem cell23_7105749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 8].length) (baseStart_7105749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7105749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7105749 prefixEnd_7105749 := by exact prefixLift 7105749
  have htrace : WordTrace (prefixWord ++ tailWord_7105749) baseStart_7105749 baseEnd_7105749 := by
    simpa [prefixWord, tailWord_7105749, baseEnd_7105749] using wordTrace_append hprefix tailTrace_7105749
  have hstable : (prefixWord ++ tailWord_7105749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7105749).length < 2 ^ (prefixWord ++ tailWord_7105749).sum := by decide
  have hdescent : baseEnd_7105749 < baseStart_7105749 := by decide
  rcases family_descends (prefixWord ++ tailWord_7105749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7105750 : List Nat := [5, 2, 1, 2, 2, 1, 2, 1, 1, 3, 3]
def baseStart_7105750 : Nat := 118140960795 + 7105750 * 2 ^ 59
def prefixEnd_7105750 : Nat := 4983230072969 + 3 ^ 40 * 7105750 * 2
def baseEnd_7105750 : Nat := 3648665160685678954146257

theorem tailTrace_7105750 : CollatzResearch.WordTrace tailWord_7105750 prefixEnd_7105750 3648665160685678954146257 := by
  unfold tailWord_7105750
  simp only [CollatzResearch.WordTrace]
  refine ⟨16197999625443049395514169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 172778662671392526885484469 16197999625443049395514169)
  ·
    refine ⟨12148499719082287046635627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16197999625443049395514169 12148499719082287046635627)
    ·
      refine ⟨18222749578623430569953441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12148499719082287046635627 18222749578623430569953441)
      ·
        refine ⟨13667062183967572927465081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18222749578623430569953441 13667062183967572927465081)
        ·
          refine ⟨10250296637975679695598811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13667062183967572927465081 10250296637975679695598811)
          ·
            refine ⟨15375444956963519543398217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10250296637975679695598811 15375444956963519543398217)
            ·
              refine ⟨11531583717722639657548663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15375444956963519543398217 11531583717722639657548663)
              ·
                refine ⟨17297375576583959486322995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11531583717722639657548663 17297375576583959486322995)
                ·
                  refine ⟨25946063364875939229484493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17297375576583959486322995 25946063364875939229484493)
                  ·
                    refine ⟨9729773761828477211056685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25946063364875939229484493 9729773761828477211056685)
                    ·
                      refine ⟨3648665160685678954146257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9729773761828477211056685 3648665160685678954146257)
                      ·
                        rfl

theorem cell23_7105750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_7105750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7105750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7105750 prefixEnd_7105750 := by exact prefixLift 7105750
  have htrace : WordTrace (prefixWord ++ tailWord_7105750) baseStart_7105750 baseEnd_7105750 := by
    simpa [prefixWord, tailWord_7105750, baseEnd_7105750] using wordTrace_append hprefix tailTrace_7105750
  have hstable : (prefixWord ++ tailWord_7105750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7105750).length < 2 ^ (prefixWord ++ tailWord_7105750).sum := by decide
  have hdescent : baseEnd_7105750 < baseStart_7105750 := by decide
  rcases family_descends (prefixWord ++ tailWord_7105750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7105773 : List Nat := [1, 5, 1, 2, 2, 1, 2, 2, 1, 4, 2]
def baseStart_7105773 : Nat := 118140960795 + 7105773 * 2 ^ 59
def prefixEnd_7105773 : Nat := 4983230072969 + 3 ^ 40 * 7105773 * 2
def baseEnd_7105773 : Nat := 3648676970740732364158651

theorem tailTrace_7105773 : CollatzResearch.WordTrace tailWord_7105773 prefixEnd_7105773 3648676970740732364158651 := by
  unfold tailWord_7105773
  simp only [CollatzResearch.WordTrace]
  refine ⟨259168832886005465256313973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172779221924003643504209315 259168832886005465256313973)
  ·
    refine ⟨24297078083063012367779435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 259168832886005465256313973 24297078083063012367779435)
    ·
      refine ⟨36445617124594518551669153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24297078083063012367779435 36445617124594518551669153)
      ·
        refine ⟨27334212843445888913751865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36445617124594518551669153 27334212843445888913751865)
        ·
          refine ⟨20500659632584416685313899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27334212843445888913751865 20500659632584416685313899)
          ·
            refine ⟨30750989448876625027970849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20500659632584416685313899 30750989448876625027970849)
            ·
              refine ⟨23063242086657468770978137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30750989448876625027970849 23063242086657468770978137)
              ·
                refine ⟨17297431564993101578233603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23063242086657468770978137 17297431564993101578233603)
                ·
                  refine ⟨25946147347489652367350405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17297431564993101578233603 25946147347489652367350405)
                  ·
                    refine ⟨4864902627654309818878201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25946147347489652367350405 4864902627654309818878201)
                    ·
                      refine ⟨3648676970740732364158651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4864902627654309818878201 3648676970740732364158651)
                      ·
                        rfl

theorem cell23_7105773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 2, 1, 4, 2].length) (baseStart_7105773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7105773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7105773 prefixEnd_7105773 := by exact prefixLift 7105773
  have htrace : WordTrace (prefixWord ++ tailWord_7105773) baseStart_7105773 baseEnd_7105773 := by
    simpa [prefixWord, tailWord_7105773, baseEnd_7105773] using wordTrace_append hprefix tailTrace_7105773
  have hstable : (prefixWord ++ tailWord_7105773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7105773).length < 2 ^ (prefixWord ++ tailWord_7105773).sum := by decide
  have hdescent : baseEnd_7105773 < baseStart_7105773 := by decide
  rcases family_descends (prefixWord ++ tailWord_7105773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7105790 : List Nat := [4, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2]
def baseStart_7105790 : Nat := 118140960795 + 7105790 * 2 ^ 59
def prefixEnd_7105790 : Nat := 4983230072969 + 3 ^ 40 * 7105790 * 2
def baseEnd_7105790 : Nat := 3648685699911858797646073

theorem tailTrace_7105790 : CollatzResearch.WordTrace tailWord_7105790 prefixEnd_7105790 3648685699911858797646073 := by
  unfold tailWord_7105790
  simp only [CollatzResearch.WordTrace]
  refine ⟨32396181615867984644960353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172779635284629251439788549 32396181615867984644960353)
  ·
    refine ⟨24297136211900988483720265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32396181615867984644960353 24297136211900988483720265)
    ·
      refine ⟨18222852158925741362790199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24297136211900988483720265 18222852158925741362790199)
      ·
        refine ⟨27334278238388612044185299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18222852158925741362790199 27334278238388612044185299)
        ·
          refine ⟨41001417357582918066277949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27334278238388612044185299 41001417357582918066277949)
          ·
            refine ⟨15375531509093594274854231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41001417357582918066277949 15375531509093594274854231)
            ·
              refine ⟨23063297263640391412281347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15375531509093594274854231 23063297263640391412281347)
              ·
                refine ⟨34594945895460587118422021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23063297263640391412281347 34594945895460587118422021)
                ·
                  refine ⟨6486552355398860084704129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34594945895460587118422021 6486552355398860084704129)
                  ·
                    refine ⟨4864914266549145063528097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6486552355398860084704129 4864914266549145063528097)
                    ·
                      refine ⟨3648685699911858797646073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4864914266549145063528097 3648685699911858797646073)
                      ·
                        rfl

theorem cell23_7105790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2].length) (baseStart_7105790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7105790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7105790 prefixEnd_7105790 := by exact prefixLift 7105790
  have htrace : WordTrace (prefixWord ++ tailWord_7105790) baseStart_7105790 baseEnd_7105790 := by
    simpa [prefixWord, tailWord_7105790, baseEnd_7105790] using wordTrace_append hprefix tailTrace_7105790
  have hstable : (prefixWord ++ tailWord_7105790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7105790).length < 2 ^ (prefixWord ++ tailWord_7105790).sum := by decide
  have hdescent : baseEnd_7105790 < baseStart_7105790 := by decide
  rcases family_descends (prefixWord ++ tailWord_7105790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7105796 : List Nat := [2, 3, 2, 2, 2, 2, 2, 1, 7]
def baseStart_7105796 : Nat := 118140960795 + 7105796 * 2 ^ 59
def prefixEnd_7105796 : Nat := 4983230072969 + 3 ^ 40 * 7105796 * 2
def baseEnd_7105796 : Nat := 405409864532865086019005

theorem tailTrace_7105796 : CollatzResearch.WordTrace tailWord_7105796 prefixEnd_7105796 405409864532865086019005 := by
  unfold tailWord_7105796
  simp only [CollatzResearch.WordTrace]
  refine ⟨129584835882461070092200621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172779781176614760122934161 129584835882461070092200621)
  ·
    refine ⟨48594313455922901284575233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129584835882461070092200621 48594313455922901284575233)
    ·
      refine ⟨36445735091942175963431425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48594313455922901284575233 36445735091942175963431425)
      ·
        refine ⟨27334301318956631972573569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36445735091942175963431425 27334301318956631972573569)
        ·
          refine ⟨20500725989217473979430177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27334301318956631972573569 20500725989217473979430177)
          ·
            refine ⟨15375544491913105484572633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20500725989217473979430177 15375544491913105484572633)
            ·
              refine ⟨11531658368934829113429475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15375544491913105484572633 11531658368934829113429475)
              ·
                refine ⟨17297487553402243670144213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11531658368934829113429475 17297487553402243670144213)
                ·
                  refine ⟨405409864532865086019005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17297487553402243670144213 405409864532865086019005)
                  ·
                    rfl

theorem cell23_7105796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 1, 7].length) (baseStart_7105796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7105796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7105796 prefixEnd_7105796 := by exact prefixLift 7105796
  have htrace : WordTrace (prefixWord ++ tailWord_7105796) baseStart_7105796 baseEnd_7105796 := by
    simpa [prefixWord, tailWord_7105796, baseEnd_7105796] using wordTrace_append hprefix tailTrace_7105796
  have hstable : (prefixWord ++ tailWord_7105796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7105796).length < 2 ^ (prefixWord ++ tailWord_7105796).sum := by decide
  have hdescent : baseEnd_7105796 < baseStart_7105796 := by decide
  rcases family_descends (prefixWord ++ tailWord_7105796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7105806 : List Nat := [4, 1, 1, 2, 1, 3, 2, 1, 2, 3, 3]
def baseStart_7105806 : Nat := 118140960795 + 7105806 * 2 ^ 59
def prefixEnd_7105806 : Nat := 4983230072969 + 3 ^ 40 * 7105806 * 2
def baseEnd_7105806 : Nat := 3648693915602330735045999

theorem tailTrace_7105806 : CollatzResearch.WordTrace tailWord_7105806 prefixEnd_7105806 3648693915602330735045999 := by
  unfold tailWord_7105806
  simp only [CollatzResearch.WordTrace]
  refine ⟨32396254561860738986533159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172780024329923941261510181 32396254561860738986533159)
  ·
    refine ⟨48594381842791108479799739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32396254561860738986533159 48594381842791108479799739)
    ·
      refine ⟨72891572764186662719699609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48594381842791108479799739 72891572764186662719699609)
      ·
        refine ⟨54668679573139997039774707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72891572764186662719699609 54668679573139997039774707)
        ·
          refine ⟨82003019359709995559662061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54668679573139997039774707 82003019359709995559662061)
          ·
            refine ⟨30751132259891248334873273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82003019359709995559662061 30751132259891248334873273)
            ·
              refine ⟨23063349194918436251154955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30751132259891248334873273 23063349194918436251154955)
              ·
                refine ⟨34595023792377654376732433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23063349194918436251154955 34595023792377654376732433)
                ·
                  refine ⟨25946267844283240782549325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34595023792377654376732433 25946267844283240782549325)
                  ·
                    refine ⟨9729850441606215293455997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25946267844283240782549325 9729850441606215293455997)
                    ·
                      refine ⟨3648693915602330735045999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9729850441606215293455997 3648693915602330735045999)
                      ·
                        rfl

theorem cell23_7105806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 2, 3, 3].length) (baseStart_7105806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7105806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7105806 prefixEnd_7105806 := by exact prefixLift 7105806
  have htrace : WordTrace (prefixWord ++ tailWord_7105806) baseStart_7105806 baseEnd_7105806 := by
    simpa [prefixWord, tailWord_7105806, baseEnd_7105806] using wordTrace_append hprefix tailTrace_7105806
  have hstable : (prefixWord ++ tailWord_7105806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7105806).length < 2 ^ (prefixWord ++ tailWord_7105806).sum := by decide
  have hdescent : baseEnd_7105806 < baseStart_7105806 := by decide
  rcases family_descends (prefixWord ++ tailWord_7105806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7105853 : List Nat := [1, 4, 1, 5, 1, 1, 1, 1, 1, 2, 5]
def baseStart_7105853 : Nat := 118140960795 + 7105853 * 2 ^ 59
def prefixEnd_7105853 : Nat := 4983230072969 + 3 ^ 40 * 7105853 * 2
def baseEnd_7105853 : Nat := 3648718049193092051158283

theorem tailTrace_7105853 : CollatzResearch.WordTrace tailWord_7105853 prefixEnd_7105853 3648718049193092051158283 := by
  unfold tailWord_7105853
  simp only [CollatzResearch.WordTrace]
  refine ⟨259171750725715638919226213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172781167150477092612817475 259171750725715638919226213)
  ·
    refine ⟨48594703261071682297354915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 259171750725715638919226213 48594703261071682297354915)
    ·
      refine ⟨72892054891607523446032373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48594703261071682297354915 72892054891607523446032373)
      ·
        refine ⟨6833630146088205323065535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72892054891607523446032373 6833630146088205323065535)
        ·
          refine ⟨10250445219132307984598303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6833630146088205323065535 10250445219132307984598303)
          ·
            refine ⟨15375667828698461976897455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10250445219132307984598303 15375667828698461976897455)
            ·
              refine ⟨23063501743047692965346183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15375667828698461976897455 23063501743047692965346183)
              ·
                refine ⟨34595252614571539448019275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23063501743047692965346183 34595252614571539448019275)
                ·
                  refine ⟨51892878921857309172028913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34595252614571539448019275 51892878921857309172028913)
                  ·
                    refine ⟨38919659191392981879021685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51892878921857309172028913 38919659191392981879021685)
                    ·
                      refine ⟨3648718049193092051158283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38919659191392981879021685 3648718049193092051158283)
                      ·
                        rfl

theorem cell23_7105853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_7105853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7105853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7105853 prefixEnd_7105853 := by exact prefixLift 7105853
  have htrace : WordTrace (prefixWord ++ tailWord_7105853) baseStart_7105853 baseEnd_7105853 := by
    simpa [prefixWord, tailWord_7105853, baseEnd_7105853] using wordTrace_append hprefix tailTrace_7105853
  have hstable : (prefixWord ++ tailWord_7105853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7105853).length < 2 ^ (prefixWord ++ tailWord_7105853).sum := by decide
  have hdescent : baseEnd_7105853 < baseStart_7105853 := by decide
  rcases family_descends (prefixWord ++ tailWord_7105853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7105890 : List Nat := [3, 3, 2, 1, 1, 1, 2, 5, 1, 4]
def baseStart_7105890 : Nat := 118140960795 + 7105890 * 2 ^ 59
def prefixEnd_7105890 : Nat := 4983230072969 + 3 ^ 40 * 7105890 * 2
def baseEnd_7105890 : Nat := 1216245682659102802131871

theorem tailTrace_7105890 : CollatzResearch.WordTrace tailWord_7105890 prefixEnd_7105890 1216245682659102802131871 := by
  unfold tailWord_7105890
  simp only [CollatzResearch.WordTrace]
  refine ⟨64793275056645398559580781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172782066817721062825548749 64793275056645398559580781)
  ·
    refine ⟨24297478146242024459842793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64793275056645398559580781 24297478146242024459842793)
    ·
      refine ⟨18223108609681518344882095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24297478146242024459842793 18223108609681518344882095)
      ·
        refine ⟨27334662914522277517323143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18223108609681518344882095 27334662914522277517323143)
        ·
          refine ⟨41001994371783416275984715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27334662914522277517323143 41001994371783416275984715)
          ·
            refine ⟨61502991557675124413977073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41001994371783416275984715 61502991557675124413977073)
            ·
              refine ⟨46127243668256343310482805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61502991557675124413977073 46127243668256343310482805)
              ·
                refine ⟨4324429093899032185357763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46127243668256343310482805 4324429093899032185357763)
                ·
                  refine ⟨6486643640848548278036645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4324429093899032185357763 6486643640848548278036645)
                  ·
                    refine ⟨1216245682659102802131871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6486643640848548278036645 1216245682659102802131871)
                    ·
                      rfl

theorem cell23_7105890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_7105890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7105890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7105890 prefixEnd_7105890 := by exact prefixLift 7105890
  have htrace : WordTrace (prefixWord ++ tailWord_7105890) baseStart_7105890 baseEnd_7105890 := by
    simpa [prefixWord, tailWord_7105890, baseEnd_7105890] using wordTrace_append hprefix tailTrace_7105890
  have hstable : (prefixWord ++ tailWord_7105890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7105890).length < 2 ^ (prefixWord ++ tailWord_7105890).sum := by decide
  have hdescent : baseEnd_7105890 < baseStart_7105890 := by decide
  rcases family_descends (prefixWord ++ tailWord_7105890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7105899 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 7, 5]
def baseStart_7105899 : Nat := 118140960795 + 7105899 * 2 ^ 59
def prefixEnd_7105899 : Nat := 4983230072969 + 3 ^ 40 * 7105899 * 2
def baseEnd_7105899 : Nat := 1216247223101066290394357

theorem tailTrace_7105899 : CollatzResearch.WordTrace tailWord_7105899 prefixEnd_7105899 1216247223101066290394357 := by
  unfold tailWord_7105899
  simp only [CollatzResearch.WordTrace]
  refine ⟨259173428483548988775400751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172782285655699325850267167 259173428483548988775400751)
  ·
    refine ⟨388760142725323483163101127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259173428483548988775400751 388760142725323483163101127)
    ·
      refine ⟨583140214087985224744651691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388760142725323483163101127 583140214087985224744651691)
      ·
        refine ⟨874710321131977837116977537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 583140214087985224744651691 874710321131977837116977537)
        ·
          refine ⟨656032740848983377837733153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 874710321131977837116977537 656032740848983377837733153)
          ·
            refine ⟨492024555636737533378299865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 656032740848983377837733153 492024555636737533378299865)
            ·
              refine ⟨369018416727553150033724899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 492024555636737533378299865 369018416727553150033724899)
              ·
                refine ⟨553527625091329725050587349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 369018416727553150033724899 553527625091329725050587349)
                ·
                  refine ⟨12973303713078040430873141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 553527625091329725050587349 12973303713078040430873141)
                  ·
                    refine ⟨1216247223101066290394357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12973303713078040430873141 1216247223101066290394357)
                    ·
                      rfl

theorem cell23_7105899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 7, 5].length) (baseStart_7105899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7105899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7105899 prefixEnd_7105899 := by exact prefixLift 7105899
  have htrace : WordTrace (prefixWord ++ tailWord_7105899) baseStart_7105899 baseEnd_7105899 := by
    simpa [prefixWord, tailWord_7105899, baseEnd_7105899] using wordTrace_append hprefix tailTrace_7105899
  have hstable : (prefixWord ++ tailWord_7105899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7105899).length < 2 ^ (prefixWord ++ tailWord_7105899).sum := by decide
  have hdescent : baseEnd_7105899 < baseStart_7105899 := by decide
  rcases family_descends (prefixWord ++ tailWord_7105899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7105919 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 4]
def baseStart_7105919 : Nat := 118140960795 + 7105919 * 2 ^ 59
def prefixEnd_7105919 : Nat := 4983230072969 + 3 ^ 40 * 7105919 * 2
def baseEnd_7105919 : Nat := 3648751938916288792932979

theorem tailTrace_7105919 : CollatzResearch.WordTrace tailWord_7105919 prefixEnd_7105919 3648751938916288792932979 := by
  unfold tailWord_7105919
  simp only [CollatzResearch.WordTrace]
  refine ⟨259174157943476532191128811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172782771962317688127419207 259174157943476532191128811)
  ·
    refine ⟨388761236915214798286693217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259174157943476532191128811 388761236915214798286693217)
    ·
      refine ⟨291570927686411098715019913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 388761236915214798286693217 291570927686411098715019913)
      ·
        refine ⟨218678195764808324036264935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291570927686411098715019913 218678195764808324036264935)
        ·
          refine ⟨328017293647212486054397403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218678195764808324036264935 328017293647212486054397403)
          ·
            refine ⟨492025940470818729081596105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328017293647212486054397403 492025940470818729081596105)
            ·
              refine ⟨369019455353114046811197079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 492025940470818729081596105 369019455353114046811197079)
              ·
                refine ⟨553529183029671070216795619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 369019455353114046811197079 553529183029671070216795619)
                ·
                  refine ⟨830293774544506605325193429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 553529183029671070216795619 830293774544506605325193429)
                  ·
                    refine ⟨19460010340886873562309221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 830293774544506605325193429 19460010340886873562309221)
                    ·
                      refine ⟨3648751938916288792932979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19460010340886873562309221 3648751938916288792932979)
                      ·
                        rfl

theorem cell23_7105919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 4].length) (baseStart_7105919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7105919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7105919 prefixEnd_7105919 := by exact prefixLift 7105919
  have htrace : WordTrace (prefixWord ++ tailWord_7105919) baseStart_7105919 baseEnd_7105919 := by
    simpa [prefixWord, tailWord_7105919, baseEnd_7105919] using wordTrace_append hprefix tailTrace_7105919
  have hstable : (prefixWord ++ tailWord_7105919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7105919).length < 2 ^ (prefixWord ++ tailWord_7105919).sum := by decide
  have hdescent : baseEnd_7105919 < baseStart_7105919 := by decide
  rcases family_descends (prefixWord ++ tailWord_7105919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7105940 : List Nat := [2, 4, 2, 1, 2, 2, 1, 1, 1, 5, 2]
def baseStart_7105940 : Nat := 118140960795 + 7105940 * 2 ^ 59
def prefixEnd_7105940 : Nat := 4983230072969 + 3 ^ 40 * 7105940 * 2
def baseEnd_7105940 : Nat := 3648762722010033210770383

theorem tailTrace_7105940 : CollatzResearch.WordTrace tailWord_7105940 prefixEnd_7105940 3648762722010033210770383 := by
  unfold tailWord_7105940
  simp only [CollatzResearch.WordTrace]
  refine ⟨129587461938200226388821637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172783282584266968518428849 129587461938200226388821637)
  ·
    refine ⟨24297649113412542447904057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129587461938200226388821637 24297649113412542447904057)
    ·
      refine ⟨18223236835059406835928043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24297649113412542447904057 18223236835059406835928043)
      ·
        refine ⟨27334855252589110253892065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18223236835059406835928043 27334855252589110253892065)
        ·
          refine ⟨20501141439441832690419049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27334855252589110253892065 20501141439441832690419049)
          ·
            refine ⟨15375856079581374517814287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20501141439441832690419049 15375856079581374517814287)
            ·
              refine ⟨23063784119372061776721431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15375856079581374517814287 23063784119372061776721431)
              ·
                refine ⟨34595676179058092665082147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23063784119372061776721431 34595676179058092665082147)
                ·
                  refine ⟨51893514268587138997623221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34595676179058092665082147 51893514268587138997623221)
                  ·
                    refine ⟨4865016962680044281027177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51893514268587138997623221 4865016962680044281027177)
                    ·
                      refine ⟨3648762722010033210770383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4865016962680044281027177 3648762722010033210770383)
                      ·
                        rfl

theorem cell23_7105940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 1, 5, 2].length) (baseStart_7105940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7105940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7105940 prefixEnd_7105940 := by exact prefixLift 7105940
  have htrace : WordTrace (prefixWord ++ tailWord_7105940) baseStart_7105940 baseEnd_7105940 := by
    simpa [prefixWord, tailWord_7105940, baseEnd_7105940] using wordTrace_append hprefix tailTrace_7105940
  have hstable : (prefixWord ++ tailWord_7105940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7105940).length < 2 ^ (prefixWord ++ tailWord_7105940).sum := by decide
  have hdescent : baseEnd_7105940 < baseStart_7105940 := by decide
  rcases family_descends (prefixWord ++ tailWord_7105940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7105946 : List Nat := [3, 1, 1, 4, 1, 1, 1, 4, 1, 6]
def baseStart_7105946 : Nat := 118140960795 + 7105946 * 2 ^ 59
def prefixEnd_7105946 : Nat := 4983230072969 + 3 ^ 40 * 7105946 * 2
def baseEnd_7105946 : Nat := 1216255267631320062431785

theorem tailTrace_7105946 : CollatzResearch.WordTrace tailWord_7105946 prefixEnd_7105946 1216255267631320062431785 := by
  unfold tailWord_7105946
  simp only [CollatzResearch.WordTrace]
  refine ⟨64793785678594678950590423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172783428476252477201574461 64793785678594678950590423)
  ·
    refine ⟨97190678517892018425885635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64793785678594678950590423 97190678517892018425885635)
    ·
      refine ⟨145786017776838027638828453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97190678517892018425885635 145786017776838027638828453)
      ·
        refine ⟨27334878333157130182280335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145786017776838027638828453 27334878333157130182280335)
        ·
          refine ⟨41002317499735695273420503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27334878333157130182280335 41002317499735695273420503)
          ·
            refine ⟨61503476249603542910130755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41002317499735695273420503 61503476249603542910130755)
            ·
              refine ⟨92255214374405314365196133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61503476249603542910130755 92255214374405314365196133)
              ·
                refine ⟨17297852695200996443474275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92255214374405314365196133 17297852695200996443474275)
                ·
                  refine ⟨25946779042801494665211413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17297852695200996443474275 25946779042801494665211413)
                  ·
                    refine ⟨1216255267631320062431785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25946779042801494665211413 1216255267631320062431785)
                    ·
                      rfl

theorem cell23_7105946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 4, 1, 6].length) (baseStart_7105946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7105946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7105946 prefixEnd_7105946 := by exact prefixLift 7105946
  have htrace : WordTrace (prefixWord ++ tailWord_7105946) baseStart_7105946 baseEnd_7105946 := by
    simpa [prefixWord, tailWord_7105946, baseEnd_7105946] using wordTrace_append hprefix tailTrace_7105946
  have hstable : (prefixWord ++ tailWord_7105946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7105946).length < 2 ^ (prefixWord ++ tailWord_7105946).sum := by decide
  have hdescent : baseEnd_7105946 < baseStart_7105946 := by decide
  rcases family_descends (prefixWord ++ tailWord_7105946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7105956 : List Nat := [2, 3, 1, 2, 1, 1, 1, 5, 1, 1, 5]
def baseStart_7105956 : Nat := 118140960795 + 7105956 * 2 ^ 59
def prefixEnd_7105956 : Nat := 4983230072969 + 3 ^ 40 * 7105956 * 2
def baseEnd_7105956 : Nat := 3648770937700505148170309

theorem tailTrace_7105956 : CollatzResearch.WordTrace tailWord_7105956 prefixEnd_7105956 3648770937700505148170309 := by
  unfold tailWord_7105956
  simp only [CollatzResearch.WordTrace]
  refine ⟨129587753722171243755112861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172783671629561658340150481 129587753722171243755112861)
  ·
    refine ⟨48595407645814216408167323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129587753722171243755112861 48595407645814216408167323)
    ·
      refine ⟨72893111468721324612250985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48595407645814216408167323 72893111468721324612250985)
      ·
        refine ⟨54669833601540993459188239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72893111468721324612250985 54669833601540993459188239)
        ·
          refine ⟨82004750402311490188782359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54669833601540993459188239 82004750402311490188782359)
          ·
            refine ⟨123007125603467235283173539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82004750402311490188782359 123007125603467235283173539)
            ·
              refine ⟨184510688405200852924760309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123007125603467235283173539 184510688405200852924760309)
              ·
                refine ⟨17297877037987579961696279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 184510688405200852924760309 17297877037987579961696279)
                ·
                  refine ⟨25946815556981369942544419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17297877037987579961696279 25946815556981369942544419)
                  ·
                    refine ⟨38920223335472054913816629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25946815556981369942544419 38920223335472054913816629)
                    ·
                      refine ⟨3648770937700505148170309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38920223335472054913816629 3648770937700505148170309)
                      ·
                        rfl

theorem cell23_7105956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_7105956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7105956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7105956 prefixEnd_7105956 := by exact prefixLift 7105956
  have htrace : WordTrace (prefixWord ++ tailWord_7105956) baseStart_7105956 baseEnd_7105956 := by
    simpa [prefixWord, tailWord_7105956, baseEnd_7105956] using wordTrace_append hprefix tailTrace_7105956
  have hstable : (prefixWord ++ tailWord_7105956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7105956).length < 2 ^ (prefixWord ++ tailWord_7105956).sum := by decide
  have hdescent : baseEnd_7105956 < baseStart_7105956 := by decide
  rcases family_descends (prefixWord ++ tailWord_7105956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7105973 : List Nat := [1, 3, 3, 2, 2, 2, 1, 2, 1, 1, 5]
def baseStart_7105973 : Nat := 118140960795 + 7105973 * 2 ^ 59
def prefixEnd_7105973 : Nat := 4983230072969 + 3 ^ 40 * 7105973 * 2
def baseEnd_7105973 : Nat := 3648779666871631581657731

theorem tailTrace_7105973 : CollatzResearch.WordTrace tailWord_7105973 prefixEnd_7105973 3648779666871631581657731 := by
  unfold tailWord_7105973
  simp only [CollatzResearch.WordTrace]
  refine ⟨259176127485280899413594573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172784084990187266275729715 259176127485280899413594573)
  ·
    refine ⟨97191047806980337280097965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259176127485280899413594573 97191047806980337280097965)
    ·
      refine ⟨36446642927617626480036737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97191047806980337280097965 36446642927617626480036737)
      ·
        refine ⟨27334982195713219860027553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36446642927617626480036737 27334982195713219860027553)
        ·
          refine ⟨20501236646784914895020665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27334982195713219860027553 20501236646784914895020665)
          ·
            refine ⟨15375927485088686171265499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20501236646784914895020665 15375927485088686171265499)
            ·
              refine ⟨23063891227633029256898249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15375927485088686171265499 23063891227633029256898249)
              ·
                refine ⟨17297918420724771942673687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23063891227633029256898249 17297918420724771942673687)
                ·
                  refine ⟨25946877631087157914010531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17297918420724771942673687 25946877631087157914010531)
                  ·
                    refine ⟨38920316446630736871015797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25946877631087157914010531 38920316446630736871015797)
                    ·
                      refine ⟨3648779666871631581657731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38920316446630736871015797 3648779666871631581657731)
                      ·
                        rfl

theorem cell23_7105973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_7105973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7105973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7105973 prefixEnd_7105973 := by exact prefixLift 7105973
  have htrace : WordTrace (prefixWord ++ tailWord_7105973) baseStart_7105973 baseEnd_7105973 := by
    simpa [prefixWord, tailWord_7105973, baseEnd_7105973] using wordTrace_append hprefix tailTrace_7105973
  have hstable : (prefixWord ++ tailWord_7105973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7105973).length < 2 ^ (prefixWord ++ tailWord_7105973).sum := by decide
  have hdescent : baseEnd_7105973 < baseStart_7105973 := by decide
  rcases family_descends (prefixWord ++ tailWord_7105973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7105980 : List Nat := [2, 2, 2, 4, 2, 2, 1, 1, 1, 6]
def baseStart_7105980 : Nat := 118140960795 + 7105980 * 2 ^ 59
def prefixEnd_7105980 : Nat := 4983230072969 + 3 ^ 40 * 7105980 * 2
def baseEnd_7105980 : Nat := 1216261087078737684756733

theorem tailTrace_7105980 : CollatzResearch.WordTrace tailWord_7105980 prefixEnd_7105980 1216261087078737684756733 := by
  unfold tailWord_7105980
  simp only [CollatzResearch.WordTrace]
  refine ⟨129588191398127769804549697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172784255197503693072732929 129588191398127769804549697)
  ·
    refine ⟨97191143548595827353412273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129588191398127769804549697 97191143548595827353412273)
    ·
      refine ⟨72893357661446870515059205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97191143548595827353412273 72893357661446870515059205)
      ·
        refine ⟨13667504561521288221573601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72893357661446870515059205 13667504561521288221573601)
        ·
          refine ⟨10250628421140966166180201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13667504561521288221573601 10250628421140966166180201)
          ·
            refine ⟨7687971315855724624635151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10250628421140966166180201 7687971315855724624635151)
            ·
              refine ⟨11531956973783586936952727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7687971315855724624635151 11531956973783586936952727)
              ·
                refine ⟨17297935460675380405429091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11531956973783586936952727 17297935460675380405429091)
                ·
                  refine ⟨25946903191013070608143637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17297935460675380405429091 25946903191013070608143637)
                  ·
                    refine ⟨1216261087078737684756733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25946903191013070608143637 1216261087078737684756733)
                    ·
                      rfl

theorem cell23_7105980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 1, 1, 6].length) (baseStart_7105980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7105980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7105980 prefixEnd_7105980 := by exact prefixLift 7105980
  have htrace : WordTrace (prefixWord ++ tailWord_7105980) baseStart_7105980 baseEnd_7105980 := by
    simpa [prefixWord, tailWord_7105980, baseEnd_7105980] using wordTrace_append hprefix tailTrace_7105980
  have hstable : (prefixWord ++ tailWord_7105980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7105980).length < 2 ^ (prefixWord ++ tailWord_7105980).sum := by decide
  have hdescent : baseEnd_7105980 < baseStart_7105980 := by decide
  rcases family_descends (prefixWord ++ tailWord_7105980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7106021 : List Nat := [1, 3, 1, 5, 1, 2, 3, 2, 1, 2, 2]
def baseStart_7106021 : Nat := 118140960795 + 7106021 * 2 ^ 59
def prefixEnd_7106021 : Nat := 4983230072969 + 3 ^ 40 * 7106021 * 2
def baseEnd_7106021 : Nat := 3648804313943047393857511

theorem tailTrace_7106021 : CollatzResearch.WordTrace tailWord_7106021 prefixEnd_7106021 3648804313943047393857511 := by
  unfold tailWord_7106021
  simp only [CollatzResearch.WordTrace]
  refine ⟨259177878189107003611341917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172785252126071335740894611 259177878189107003611341917)
  ·
    refine ⟨97191704320915126354253219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259177878189107003611341917 97191704320915126354253219)
    ·
      refine ⟨145787556481372689531379829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97191704320915126354253219 145787556481372689531379829)
      ·
        refine ⟨13667583420128689643566859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 145787556481372689531379829 13667583420128689643566859)
        ·
          refine ⟨20501375130193034465350289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13667583420128689643566859 20501375130193034465350289)
          ·
            refine ⟨15376031347644775849012717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20501375130193034465350289 15376031347644775849012717)
            ·
              refine ⟨5766011755366790943379769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15376031347644775849012717 5766011755366790943379769)
              ·
                refine ⟨4324508816525093207534827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5766011755366790943379769 4324508816525093207534827)
                ·
                  refine ⟨6486763224787639811302241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4324508816525093207534827 6486763224787639811302241)
                  ·
                    refine ⟨4865072418590729858476681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6486763224787639811302241 4865072418590729858476681)
                    ·
                      refine ⟨3648804313943047393857511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4865072418590729858476681 3648804313943047393857511)
                      ·
                        rfl

theorem cell23_7106021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_7106021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7106021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7106021 prefixEnd_7106021 := by exact prefixLift 7106021
  have htrace : WordTrace (prefixWord ++ tailWord_7106021) baseStart_7106021 baseEnd_7106021 := by
    simpa [prefixWord, tailWord_7106021, baseEnd_7106021] using wordTrace_append hprefix tailTrace_7106021
  have hstable : (prefixWord ++ tailWord_7106021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7106021).length < 2 ^ (prefixWord ++ tailWord_7106021).sum := by decide
  have hdescent : baseEnd_7106021 < baseStart_7106021 := by decide
  rcases family_descends (prefixWord ++ tailWord_7106021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7106030 : List Nat := [4, 1, 2, 1, 2, 1, 2, 2, 3, 3, 2]
def baseStart_7106030 : Nat := 118140960795 + 7106030 * 2 ^ 59
def prefixEnd_7106030 : Nat := 4983230072969 + 3 ^ 40 * 7106030 * 2
def baseEnd_7106030 : Nat := 3648808935268937858644969

theorem tailTrace_7106030 : CollatzResearch.WordTrace tailWord_7106030 prefixEnd_7106030 3648808935268937858644969 := by
  unfold tailWord_7106030
  simp only [CollatzResearch.WordTrace]
  refine ⟨32397275805759299768552443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172785470964049598765613029 32397275805759299768552443)
  ·
    refine ⟨48595913708638949652828665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32397275805759299768552443 48595913708638949652828665)
    ·
      refine ⟨36446935281479212239621499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48595913708638949652828665 36446935281479212239621499)
      ·
        refine ⟨54670402922218818359432249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36446935281479212239621499 54670402922218818359432249)
        ·
          refine ⟨41002802191664113769574187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54670402922218818359432249 41002802191664113769574187)
          ·
            refine ⟨61504203287496170654361281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41002802191664113769574187 61504203287496170654361281)
            ·
              refine ⟨46128152465622127990770961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61504203287496170654361281 46128152465622127990770961)
              ·
                refine ⟨34596114349216595993078221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46128152465622127990770961 34596114349216595993078221)
                ·
                  refine ⟨12973542880956223497404333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34596114349216595993078221 12973542880956223497404333)
                  ·
                    refine ⟨4865078580358583811526625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12973542880956223497404333 4865078580358583811526625)
                    ·
                      refine ⟨3648808935268937858644969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4865078580358583811526625 3648808935268937858644969)
                      ·
                        rfl

theorem cell23_7106030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 3, 3, 2].length) (baseStart_7106030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7106030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7106030 prefixEnd_7106030 := by exact prefixLift 7106030
  have htrace : WordTrace (prefixWord ++ tailWord_7106030) baseStart_7106030 baseEnd_7106030 := by
    simpa [prefixWord, tailWord_7106030, baseEnd_7106030] using wordTrace_append hprefix tailTrace_7106030
  have hstable : (prefixWord ++ tailWord_7106030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7106030).length < 2 ^ (prefixWord ++ tailWord_7106030).sum := by decide
  have hdescent : baseEnd_7106030 < baseStart_7106030 := by decide
  rcases family_descends (prefixWord ++ tailWord_7106030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7106094 : List Nat := [4, 1, 3, 1, 2, 1, 2, 3, 2, 2, 2]
def baseStart_7106094 : Nat := 118140960795 + 7106094 * 2 ^ 59
def prefixEnd_7106094 : Nat := 4983230072969 + 3 ^ 40 * 7106094 * 2
def baseEnd_7106094 : Nat := 3648841798030825608244675

theorem tailTrace_7106094 : CollatzResearch.WordTrace tailWord_7106094 prefixEnd_7106094 3648841798030825608244675 := by
  unfold tailWord_7106094
  simp only [CollatzResearch.WordTrace]
  refine ⟨32397567589730317134843667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172787027145228358052499557 32397567589730317134843667)
  ·
    refine ⟨48596351384595475702265501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32397567589730317134843667 48596351384595475702265501)
    ·
      refine ⟨18223631769223303388349563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48596351384595475702265501 18223631769223303388349563)
      ·
        refine ⟨27335447653834955082524345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18223631769223303388349563 27335447653834955082524345)
        ·
          refine ⟨20501585740376216311893259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27335447653834955082524345 20501585740376216311893259)
          ·
            refine ⟨30752378610564324467839889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20501585740376216311893259 30752378610564324467839889)
            ·
              refine ⟨23064283957923243350879917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30752378610564324467839889 23064283957923243350879917)
              ·
                refine ⟨8649106484221216256579969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23064283957923243350879917 8649106484221216256579969)
                ·
                  refine ⟨6486829863165912192434977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8649106484221216256579969 6486829863165912192434977)
                  ·
                    refine ⟨4865122397374434144326233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6486829863165912192434977 4865122397374434144326233)
                    ·
                      refine ⟨3648841798030825608244675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4865122397374434144326233 3648841798030825608244675)
                      ·
                        rfl

theorem cell23_7106094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 3, 2, 2, 2].length) (baseStart_7106094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7106094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7106094 prefixEnd_7106094 := by exact prefixLift 7106094
  have htrace : WordTrace (prefixWord ++ tailWord_7106094) baseStart_7106094 baseEnd_7106094 := by
    simpa [prefixWord, tailWord_7106094, baseEnd_7106094] using wordTrace_append hprefix tailTrace_7106094
  have hstable : (prefixWord ++ tailWord_7106094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7106094).length < 2 ^ (prefixWord ++ tailWord_7106094).sum := by decide
  have hdescent : baseEnd_7106094 < baseStart_7106094 := by decide
  rcases family_descends (prefixWord ++ tailWord_7106094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7106096 : List Nat := [2, 1, 1, 1, 2, 3, 1, 4, 1, 7]
def baseStart_7106096 : Nat := 118140960795 + 7106096 * 2 ^ 59
def prefixEnd_7106096 : Nat := 4983230072969 + 3 ^ 40 * 7106096 * 2
def baseEnd_7106096 : Nat := 1216280941664044866806555

theorem tailTrace_7106096 : CollatzResearch.WordTrace tailWord_7106096 prefixEnd_7106096 1216280941664044866806555 := by
  unfold tailWord_7106096
  simp only [CollatzResearch.WordTrace]
  refine ⟨129590306831917645710161071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172787075775890194280214761 129590306831917645710161071)
  ·
    refine ⟨194385460247876468565241607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129590306831917645710161071 194385460247876468565241607)
    ·
      refine ⟨291578190371814702847862411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194385460247876468565241607 291578190371814702847862411)
      ·
        refine ⟨437367285557722054271793617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291578190371814702847862411 437367285557722054271793617)
        ·
          refine ⟨328025464168291540703845213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 437367285557722054271793617 328025464168291540703845213)
          ·
            refine ⟨123009549063109327763941955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 328025464168291540703845213 123009549063109327763941955)
            ·
              refine ⟨184514323594663991645912933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123009549063109327763941955 184514323594663991645912933)
              ·
                refine ⟨34596435673999498433608675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 184514323594663991645912933 34596435673999498433608675)
                ·
                  refine ⟨51894653510999247650413013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34596435673999498433608675 51894653510999247650413013)
                  ·
                    refine ⟨1216280941664044866806555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51894653510999247650413013 1216280941664044866806555)
                    ·
                      rfl

theorem cell23_7106096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 1, 7].length) (baseStart_7106096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7106096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7106096 prefixEnd_7106096 := by exact prefixLift 7106096
  have htrace : WordTrace (prefixWord ++ tailWord_7106096) baseStart_7106096 baseEnd_7106096 := by
    simpa [prefixWord, tailWord_7106096, baseEnd_7106096] using wordTrace_append hprefix tailTrace_7106096
  have hstable : (prefixWord ++ tailWord_7106096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7106096).length < 2 ^ (prefixWord ++ tailWord_7106096).sum := by decide
  have hdescent : baseEnd_7106096 < baseStart_7106096 := by decide
  rcases family_descends (prefixWord ++ tailWord_7106096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7106113 : List Nat := [1, 2, 5, 1, 1, 1, 3, 1, 1, 7]
def baseStart_7106113 : Nat := 118140960795 + 7106113 * 2 ^ 59
def prefixEnd_7106113 : Nat := 4983230072969 + 3 ^ 40 * 7106113 * 2
def baseEnd_7106113 : Nat := 1216283851387753677969029

theorem tailTrace_7106113 : CollatzResearch.WordTrace tailWord_7106113 prefixEnd_7106113 1216283851387753677969029 := by
  unfold tailWord_7106113
  simp only [CollatzResearch.WordTrace]
  refine ⟨259181233704773703323690993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172787489136515802215793995 259181233704773703323690993)
  ·
    refine ⟨194385925278580277492768245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259181233704773703323690993 194385925278580277492768245)
    ·
      refine ⟨18223680494866901014947023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 194385925278580277492768245 18223680494866901014947023)
      ·
        refine ⟨27335520742300351522420535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18223680494866901014947023 27335520742300351522420535)
        ·
          refine ⟨41003281113450527283630803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27335520742300351522420535 41003281113450527283630803)
          ·
            refine ⟨61504921670175790925446205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41003281113450527283630803 61504921670175790925446205)
            ·
              refine ⟨23064345626315921597042327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61504921670175790925446205 23064345626315921597042327)
              ·
                refine ⟨34596518439473882395563491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23064345626315921597042327 34596518439473882395563491)
                ·
                  refine ⟨51894777659210823593345237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34596518439473882395563491 51894777659210823593345237)
                  ·
                    refine ⟨1216283851387753677969029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51894777659210823593345237 1216283851387753677969029)
                    ·
                      rfl

theorem cell23_7106113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_7106113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7106113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7106113 prefixEnd_7106113 := by exact prefixLift 7106113
  have htrace : WordTrace (prefixWord ++ tailWord_7106113) baseStart_7106113 baseEnd_7106113 := by
    simpa [prefixWord, tailWord_7106113, baseEnd_7106113] using wordTrace_append hprefix tailTrace_7106113
  have hstable : (prefixWord ++ tailWord_7106113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7106113).length < 2 ^ (prefixWord ++ tailWord_7106113).sum := by decide
  have hdescent : baseEnd_7106113 < baseStart_7106113 := by decide
  rcases family_descends (prefixWord ++ tailWord_7106113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7106133 : List Nat := [1, 3, 2, 2, 1, 1, 1, 3, 4, 1, 4]
def baseStart_7106133 : Nat := 118140960795 + 7106133 * 2 ^ 59
def prefixEnd_7106133 : Nat := 4983230072969 + 3 ^ 40 * 7106133 * 2
def baseEnd_7106133 : Nat := 3648861823776350955656995

theorem tailTrace_7106133 : CollatzResearch.WordTrace tailWord_7106133 prefixEnd_7106133 3648861823776350955656995 := by
  unfold tailWord_7106133
  simp only [CollatzResearch.WordTrace]
  refine ⟨259181963164701246739419053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172787975443134164492946035 259181963164701246739419053)
  ·
    refine ⟨97193236186762967527282145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259181963164701246739419053 97193236186762967527282145)
    ·
      refine ⟨72894927140072225645461609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97193236186762967527282145 72894927140072225645461609)
      ·
        refine ⟨54671195355054169234096207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72894927140072225645461609 54671195355054169234096207)
        ·
          refine ⟨82006793032581253851144311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54671195355054169234096207 82006793032581253851144311)
          ·
            refine ⟨123010189548871880776716467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82006793032581253851144311 123010189548871880776716467)
            ·
              refine ⟨184515284323307821165074701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123010189548871880776716467 184515284323307821165074701)
              ·
                refine ⟨69193231621240432936903013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 184515284323307821165074701 69193231621240432936903013)
                ·
                  refine ⟨12973730928982581175669315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69193231621240432936903013 12973730928982581175669315)
                  ·
                    refine ⟨19460596393473871763503973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12973730928982581175669315 19460596393473871763503973)
                    ·
                      refine ⟨3648861823776350955656995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19460596393473871763503973 3648861823776350955656995)
                      ·
                        rfl

theorem cell23_7106133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_7106133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7106133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7106133 prefixEnd_7106133 := by exact prefixLift 7106133
  have htrace : WordTrace (prefixWord ++ tailWord_7106133) baseStart_7106133 baseEnd_7106133 := by
    simpa [prefixWord, tailWord_7106133, baseEnd_7106133] using wordTrace_append hprefix tailTrace_7106133
  have hstable : (prefixWord ++ tailWord_7106133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7106133).length < 2 ^ (prefixWord ++ tailWord_7106133).sum := by decide
  have hdescent : baseEnd_7106133 < baseStart_7106133 := by decide
  rcases family_descends (prefixWord ++ tailWord_7106133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7106134 : List Nat := [5, 2, 2, 2, 1, 1, 2, 1, 7]
def baseStart_7106134 : Nat := 118140960795 + 7106134 * 2 ^ 59
def prefixEnd_7106134 : Nat := 4983230072969 + 3 ^ 40 * 7106134 * 2
def baseEnd_7106134 : Nat := 405429148584111716860499

theorem tailTrace_7106134 : CollatzResearch.WordTrace tailWord_7106134 prefixEnd_7106134 405429148584111716860499 := by
  unfold tailWord_7106134
  simp only [CollatzResearch.WordTrace]
  refine ⟨16198874977356101494387841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 172787999758465082606803637 16198874977356101494387841)
  ·
    refine ⟨12149156233017076120790881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16198874977356101494387841 12149156233017076120790881)
    ·
      refine ⟨9111867174762807090593161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12149156233017076120790881 9111867174762807090593161)
      ·
        refine ⟨6833900381072105317944871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9111867174762807090593161 6833900381072105317944871)
        ·
          refine ⟨10250850571608157976917307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6833900381072105317944871 10250850571608157976917307)
          ·
            refine ⟨15376275857412236965375961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10250850571608157976917307 15376275857412236965375961)
            ·
              refine ⟨11532206893059177724031971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15376275857412236965375961 11532206893059177724031971)
              ·
                refine ⟨17298310339588766586047957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11532206893059177724031971 17298310339588766586047957)
                ·
                  refine ⟨405429148584111716860499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17298310339588766586047957 405429148584111716860499)
                  ·
                    rfl

theorem cell23_7106134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_7106134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7106134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7106134 prefixEnd_7106134 := by exact prefixLift 7106134
  have htrace : WordTrace (prefixWord ++ tailWord_7106134) baseStart_7106134 baseEnd_7106134 := by
    simpa [prefixWord, tailWord_7106134, baseEnd_7106134] using wordTrace_append hprefix tailTrace_7106134
  have hstable : (prefixWord ++ tailWord_7106134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7106134).length < 2 ^ (prefixWord ++ tailWord_7106134).sum := by decide
  have hdescent : baseEnd_7106134 < baseStart_7106134 := by decide
  rcases family_descends (prefixWord ++ tailWord_7106134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7106153 : List Nat := [1, 2, 1, 1, 1, 4, 3, 2, 1, 4, 3]
def baseStart_7106153 : Nat := 118140960795 + 7106153 * 2 ^ 59
def prefixEnd_7106153 : Nat := 4983230072969 + 3 ^ 40 * 7106153 * 2
def baseEnd_7106153 : Nat := 3648872093389440877406903

theorem tailTrace_7106153 : CollatzResearch.WordTrace tailWord_7106153 prefixEnd_7106153 3648872093389440877406903 := by
  unfold tailWord_7106153
  simp only [CollatzResearch.WordTrace]
  refine ⟨259182692624628790155147113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172788461749752526770098075 259182692624628790155147113)
  ·
    refine ⟨194387019468471592616360335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259182692624628790155147113 194387019468471592616360335)
    ·
      refine ⟨291580529202707388924540503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194387019468471592616360335 291580529202707388924540503)
      ·
        refine ⟨437370793804061083386810755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291580529202707388924540503 437370793804061083386810755)
        ·
          refine ⟨656056190706091625080216133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 437370793804061083386810755 656056190706091625080216133)
          ·
            refine ⟨123010535757392179702540525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 656056190706091625080216133 123010535757392179702540525)
            ·
              refine ⟨46128950909022067388452697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123010535757392179702540525 46128950909022067388452697)
              ·
                refine ⟨34596713181766550541339523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46128950909022067388452697 34596713181766550541339523)
                ·
                  refine ⟨51895069772649825812009285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34596713181766550541339523 51895069772649825812009285)
                  ·
                    refine ⟨9730325582371842339751741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51895069772649825812009285 9730325582371842339751741)
                    ·
                      refine ⟨3648872093389440877406903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9730325582371842339751741 3648872093389440877406903)
                      ·
                        rfl

theorem cell23_7106153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 4, 3].length) (baseStart_7106153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7106153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7106153 prefixEnd_7106153 := by exact prefixLift 7106153
  have htrace : WordTrace (prefixWord ++ tailWord_7106153) baseStart_7106153 baseEnd_7106153 := by
    simpa [prefixWord, tailWord_7106153, baseEnd_7106153] using wordTrace_append hprefix tailTrace_7106153
  have hstable : (prefixWord ++ tailWord_7106153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7106153).length < 2 ^ (prefixWord ++ tailWord_7106153).sum := by decide
  have hdescent : baseEnd_7106153 < baseStart_7106153 := by decide
  rcases family_descends (prefixWord ++ tailWord_7106153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7106160 : List Nat := [2, 1, 1, 1, 6, 1, 2, 2, 3, 4]
def baseStart_7106160 : Nat := 118140960795 + 7106160 * 2 ^ 59
def prefixEnd_7106160 : Nat := 4983230072969 + 3 ^ 40 * 7106160 * 2
def baseEnd_7106160 : Nat := 1216291895918007450006457

theorem tailTrace_7106160 : CollatzResearch.WordTrace tailWord_7106160 prefixEnd_7106160 1216291895918007450006457 := by
  unfold tailWord_7106160
  simp only [CollatzResearch.WordTrace]
  refine ⟨129591473967801715175325967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172788631957068953567101289 129591473967801715175325967)
  ·
    refine ⟨194387210951702572762988951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129591473967801715175325967 194387210951702572762988951)
    ·
      refine ⟨291580816427553859144483427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194387210951702572762988951 291580816427553859144483427)
      ·
        refine ⟨437371224641330788716725141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291580816427553859144483427 437371224641330788716725141)
        ·
          refine ⟨20501776155062380721096491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 437371224641330788716725141 20501776155062380721096491)
          ·
            refine ⟨30752664232593571081644737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20501776155062380721096491 30752664232593571081644737)
            ·
              refine ⟨23064498174445178311233553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30752664232593571081644737 23064498174445178311233553)
              ·
                refine ⟨17298373630833883733425165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23064498174445178311233553 17298373630833883733425165)
                ·
                  refine ⟨6486890111562706400034437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17298373630833883733425165 6486890111562706400034437)
                  ·
                    refine ⟨1216291895918007450006457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6486890111562706400034437 1216291895918007450006457)
                    ·
                      rfl

theorem cell23_7106160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 2, 3, 4].length) (baseStart_7106160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7106160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7106160 prefixEnd_7106160 := by exact prefixLift 7106160
  have htrace : WordTrace (prefixWord ++ tailWord_7106160) baseStart_7106160 baseEnd_7106160 := by
    simpa [prefixWord, tailWord_7106160, baseEnd_7106160] using wordTrace_append hprefix tailTrace_7106160
  have hstable : (prefixWord ++ tailWord_7106160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7106160).length < 2 ^ (prefixWord ++ tailWord_7106160).sum := by decide
  have hdescent : baseEnd_7106160 < baseStart_7106160 := by decide
  rcases family_descends (prefixWord ++ tailWord_7106160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7106173 : List Nat := [1, 4, 1, 1, 4, 1, 1, 2, 8]
def baseStart_7106173 : Nat := 118140960795 + 7106173 * 2 ^ 59
def prefixEnd_7106173 : Nat := 4983230072969 + 3 ^ 40 * 7106173 * 2
def baseEnd_7106173 : Nat := 405431373666947866572979

theorem tailTrace_7106173 : CollatzResearch.WordTrace tailWord_7106173 prefixEnd_7106173 405431373666947866572979 := by
  unfold tailWord_7106173
  simp only [CollatzResearch.WordTrace]
  refine ⟨259183422084556333570875173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172788948056370889047250115 259183422084556333570875173)
  ·
    refine ⟨48596891640854312544539095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 259183422084556333570875173 48596891640854312544539095)
    ·
      refine ⟨72895337461281468816808643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48596891640854312544539095 72895337461281468816808643)
      ·
        refine ⟨109343006191922203225212965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72895337461281468816808643 109343006191922203225212965)
        ·
          refine ⟨20501813660985413104727431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109343006191922203225212965 20501813660985413104727431)
          ·
            refine ⟨30752720491478119657091147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20501813660985413104727431 30752720491478119657091147)
            ·
              refine ⟨46129080737217179485636721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30752720491478119657091147 46129080737217179485636721)
              ·
                refine ⟨34596810552912884614227541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46129080737217179485636721 34596810552912884614227541)
                ·
                  refine ⟨405431373666947866572979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34596810552912884614227541 405431373666947866572979)
                  ·
                    rfl

theorem cell23_7106173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 8].length) (baseStart_7106173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7106173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7106173 prefixEnd_7106173 := by exact prefixLift 7106173
  have htrace : WordTrace (prefixWord ++ tailWord_7106173) baseStart_7106173 baseEnd_7106173 := by
    simpa [prefixWord, tailWord_7106173, baseEnd_7106173] using wordTrace_append hprefix tailTrace_7106173
  have hstable : (prefixWord ++ tailWord_7106173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7106173).length < 2 ^ (prefixWord ++ tailWord_7106173).sum := by decide
  have hdescent : baseEnd_7106173 < baseStart_7106173 := by decide
  rcases family_descends (prefixWord ++ tailWord_7106173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7106194 : List Nat := [3, 2, 3, 1, 3, 2, 1, 1, 3, 4]
def baseStart_7106194 : Nat := 118140960795 + 7106194 * 2 ^ 59
def prefixEnd_7106194 : Nat := 4983230072969 + 3 ^ 40 * 7106194 * 2
def baseEnd_7106194 : Nat := 1216297715365425072331405

theorem tailTrace_7106194 : CollatzResearch.WordTrace tailWord_7106194 prefixEnd_7106194 1216297715365425072331405 := by
  unfold tailWord_7106194
  simp only [CollatzResearch.WordTrace]
  refine ⟨64796047004370063539347409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172789458678320169438259757 64796047004370063539347409)
  ·
    refine ⟨48597035253277547654510557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64796047004370063539347409 48597035253277547654510557)
    ·
      refine ⟨18223888219979080370441459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48597035253277547654510557 18223888219979080370441459)
      ·
        refine ⟨27335832329968620555662189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18223888219979080370441459 27335832329968620555662189)
        ·
          refine ⟨10250937123738232708373321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27335832329968620555662189 10250937123738232708373321)
          ·
            refine ⟨7688202842803674531279991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10250937123738232708373321 7688202842803674531279991)
            ·
              refine ⟨11532304264205511796919987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7688202842803674531279991 11532304264205511796919987)
              ·
                refine ⟨17298456396308267695379981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11532304264205511796919987 17298456396308267695379981)
                ·
                  refine ⟨6486921148615600385767493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17298456396308267695379981 6486921148615600385767493)
                  ·
                    refine ⟨1216297715365425072331405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6486921148615600385767493 1216297715365425072331405)
                    ·
                      rfl

theorem cell23_7106194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_7106194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7106194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7106194 prefixEnd_7106194 := by exact prefixLift 7106194
  have htrace : WordTrace (prefixWord ++ tailWord_7106194) baseStart_7106194 baseEnd_7106194 := by
    simpa [prefixWord, tailWord_7106194, baseEnd_7106194] using wordTrace_append hprefix tailTrace_7106194
  have hstable : (prefixWord ++ tailWord_7106194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7106194).length < 2 ^ (prefixWord ++ tailWord_7106194).sum := by decide
  have hdescent : baseEnd_7106194 < baseStart_7106194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7106194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7106207 : List Nat := [1, 1, 2, 7, 1, 1, 1, 3, 6]
def baseStart_7106207 : Nat := 118140960795 + 7106207 * 2 ^ 59
def prefixEnd_7106207 : Nat := 4983230072969 + 3 ^ 40 * 7106207 * 2
def baseEnd_7106207 : Nat := 405433313482753740681295

theorem tailTrace_7106207 : CollatzResearch.WordTrace tailWord_7106207 prefixEnd_7106207 405433313482753740681295 := by
  unfold tailWord_7106207
  simp only [CollatzResearch.WordTrace]
  refine ⟨259184662166433157377612875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172789774777622104918408583 259184662166433157377612875)
  ·
    refine ⟨388776993249649736066419313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259184662166433157377612875 388776993249649736066419313)
    ·
      refine ⟨291582744937237302049814485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 388776993249649736066419313 291582744937237302049814485)
      ·
        refine ⟨6833970584466499266792527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 291582744937237302049814485 6833970584466499266792527)
        ·
          refine ⟨10250955876699748900188791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6833970584466499266792527 10250955876699748900188791)
          ·
            refine ⟨15376433815049623350283187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10250955876699748900188791 15376433815049623350283187)
            ·
              refine ⟨23064650722574435025424781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15376433815049623350283187 23064650722574435025424781)
              ·
                refine ⟨8649244020965413134534293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23064650722574435025424781 8649244020965413134534293)
                ·
                  refine ⟨405433313482753740681295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8649244020965413134534293 405433313482753740681295)
                  ·
                    rfl

theorem cell23_7106207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 3, 6].length) (baseStart_7106207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7106207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7106207 prefixEnd_7106207 := by exact prefixLift 7106207
  have htrace : WordTrace (prefixWord ++ tailWord_7106207) baseStart_7106207 baseEnd_7106207 := by
    simpa [prefixWord, tailWord_7106207, baseEnd_7106207] using wordTrace_append hprefix tailTrace_7106207
  have hstable : (prefixWord ++ tailWord_7106207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7106207).length < 2 ^ (prefixWord ++ tailWord_7106207).sum := by decide
  have hdescent : baseEnd_7106207 < baseStart_7106207 := by decide
  rcases family_descends (prefixWord ++ tailWord_7106207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7106227 : List Nat := [1, 1, 1, 2, 3, 3, 4, 1, 2, 3, 2]
def baseStart_7106227 : Nat := 118140960795 + 7106227 * 2 ^ 59
def prefixEnd_7106227 : Nat := 4983230072969 + 3 ^ 40 * 7106227 * 2
def baseEnd_7106227 : Nat := 3648910090957873587881563

theorem tailTrace_7106227 : CollatzResearch.WordTrace tailWord_7106227 prefixEnd_7106227 3648910090957873587881563 := by
  unfold tailWord_7106227
  simp only [CollatzResearch.WordTrace]
  refine ⟨259185391626360700793340935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172790261084240467195560623 259185391626360700793340935)
  ·
    refine ⟨388778087439541051190011403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259185391626360700793340935 388778087439541051190011403)
    ·
      refine ⟨583167131159311576785017105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388778087439541051190011403 583167131159311576785017105)
      ·
        refine ⟨437375348369483682588762829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 583167131159311576785017105 437375348369483682588762829)
        ·
          refine ⟨164015755638556380970786061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 437375348369483682588762829 164015755638556380970786061)
          ·
            refine ⟨61505908364458642864044773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164015755638556380970786061 61505908364458642864044773)
            ·
              refine ⟨11532357818335995537008395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61505908364458642864044773 11532357818335995537008395)
              ·
                refine ⟨17298536727503993305512593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11532357818335995537008395 17298536727503993305512593)
                ·
                  refine ⟨12973902545627994979134445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17298536727503993305512593 12973902545627994979134445)
                  ·
                    refine ⟨4865213454610498117175417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12973902545627994979134445 4865213454610498117175417)
                    ·
                      refine ⟨3648910090957873587881563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4865213454610498117175417 3648910090957873587881563)
                      ·
                        rfl

theorem cell23_7106227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 1, 2, 3, 2].length) (baseStart_7106227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7106227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7106227 prefixEnd_7106227 := by exact prefixLift 7106227
  have htrace : WordTrace (prefixWord ++ tailWord_7106227) baseStart_7106227 baseEnd_7106227 := by
    simpa [prefixWord, tailWord_7106227, baseEnd_7106227] using wordTrace_append hprefix tailTrace_7106227
  have hstable : (prefixWord ++ tailWord_7106227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7106227).length < 2 ^ (prefixWord ++ tailWord_7106227).sum := by decide
  have hdescent : baseEnd_7106227 < baseStart_7106227 := by decide
  rcases family_descends (prefixWord ++ tailWord_7106227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7106233 : List Nat := [1, 2, 1, 4, 1, 1, 3, 1, 3, 6]
def baseStart_7106233 : Nat := 118140960795 + 7106233 * 2 ^ 59
def prefixEnd_7106233 : Nat := 4983230072969 + 3 ^ 40 * 7106233 * 2
def baseEnd_7106233 : Nat := 1216304390613933521468845

theorem tailTrace_7106233 : CollatzResearch.WordTrace tailWord_7106233 prefixEnd_7106233 1216304390613933521468845 := by
  unfold tailWord_7106233
  simp only [CollatzResearch.WordTrace]
  refine ⟨259185610464338963818059353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172790406976225975878706235 259185610464338963818059353)
  ·
    refine ⟨194389207848254222863544515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259185610464338963818059353 194389207848254222863544515)
    ·
      refine ⟨291583811772381334295316773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194389207848254222863544515 291583811772381334295316773)
      ·
        refine ⟨54671964707321500180371895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 291583811772381334295316773 54671964707321500180371895)
        ·
          refine ⟨82007947060982250270557843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54671964707321500180371895 82007947060982250270557843)
          ·
            refine ⟨123011920591473375405836765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82007947060982250270557843 123011920591473375405836765)
            ·
              refine ⟨46129470221802515777188787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123011920591473375405836765 46129470221802515777188787)
              ·
                refine ⟨69194205332703773665783181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46129470221802515777188787 69194205332703773665783181)
                ·
                  refine ⟨25947826999763915124668693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69194205332703773665783181 25947826999763915124668693)
                  ·
                    refine ⟨1216304390613933521468845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25947826999763915124668693 1216304390613933521468845)
                    ·
                      rfl

theorem cell23_7106233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 3, 6].length) (baseStart_7106233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7106233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7106233 prefixEnd_7106233 := by exact prefixLift 7106233
  have htrace : WordTrace (prefixWord ++ tailWord_7106233) baseStart_7106233 baseEnd_7106233 := by
    simpa [prefixWord, tailWord_7106233, baseEnd_7106233] using wordTrace_append hprefix tailTrace_7106233
  have hstable : (prefixWord ++ tailWord_7106233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7106233).length < 2 ^ (prefixWord ++ tailWord_7106233).sum := by decide
  have hdescent : baseEnd_7106233 < baseStart_7106233 := by decide
  rcases family_descends (prefixWord ++ tailWord_7106233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7106237 : List Nat := [1, 4, 1, 2, 1, 2, 5, 1, 1, 5]
def baseStart_7106237 : Nat := 118140960795 + 7106237 * 2 ^ 59
def prefixEnd_7106237 : Nat := 4983230072969 + 3 ^ 40 * 7106237 * 2
def baseEnd_7106237 : Nat := 1216305075254806182918839

theorem tailTrace_7106237 : CollatzResearch.WordTrace tailWord_7106237 prefixEnd_7106237 1216305075254806182918839 := by
  unfold tailWord_7106237
  simp only [CollatzResearch.WordTrace]
  refine ⟨259185756356324472501204965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172790504237549648334136643 259185756356324472501204965)
  ·
    refine ⟨48597329316810838593975931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 259185756356324472501204965 48597329316810838593975931)
    ·
      refine ⟨72895993975216257890963897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48597329316810838593975931 72895993975216257890963897)
      ·
        refine ⟨54671995481412193418222923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72895993975216257890963897 54671995481412193418222923)
        ·
          refine ⟨82007993222118290127334385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54671995481412193418222923 82007993222118290127334385)
          ·
            refine ⟨61505994916588717595500789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82007993222118290127334385 61505994916588717595500789)
            ·
              refine ⟨5766187023430192274578199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61505994916588717595500789 5766187023430192274578199)
              ·
                refine ⟨8649280535145288411867299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5766187023430192274578199 8649280535145288411867299)
                ·
                  refine ⟨12973920802717932617800949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8649280535145288411867299 12973920802717932617800949)
                  ·
                    refine ⟨1216305075254806182918839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12973920802717932617800949 1216305075254806182918839)
                    ·
                      rfl

theorem cell23_7106237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 5, 1, 1, 5].length) (baseStart_7106237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7106237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7106237 prefixEnd_7106237 := by exact prefixLift 7106237
  have htrace : WordTrace (prefixWord ++ tailWord_7106237) baseStart_7106237 baseEnd_7106237 := by
    simpa [prefixWord, tailWord_7106237, baseEnd_7106237] using wordTrace_append hprefix tailTrace_7106237
  have hstable : (prefixWord ++ tailWord_7106237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7106237).length < 2 ^ (prefixWord ++ tailWord_7106237).sum := by decide
  have hdescent : baseEnd_7106237 < baseStart_7106237 := by decide
  rcases family_descends (prefixWord ++ tailWord_7106237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7106277 : List Nat := [1, 3, 1, 4, 1, 1, 2, 4, 1, 2, 3]
def baseStart_7106277 : Nat := 118140960795 + 7106277 * 2 ^ 59
def prefixEnd_7106277 : Nat := 4983230072969 + 3 ^ 40 * 7106277 * 2
def baseEnd_7106277 : Nat := 3648935764990598392256333

theorem tailTrace_7106277 : CollatzResearch.WordTrace tailWord_7106277 prefixEnd_7106277 3648935764990598392256333 := by
  unfold tailWord_7106277
  simp only [CollatzResearch.WordTrace]
  refine ⟨259187215276179559332661085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172791476850786372888440723 259187215276179559332661085)
  ·
    refine ⟨97195205728567334749747907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259187215276179559332661085 97195205728567334749747907)
    ·
      refine ⟨145792808592851002124621861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97195205728567334749747907 145792808592851002124621861)
      ·
        refine ⟨27336151611159562898366599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145792808592851002124621861 27336151611159562898366599)
        ·
          refine ⟨41004227416739344347549899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27336151611159562898366599 41004227416739344347549899)
          ·
            refine ⟨61506341125109016521324849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41004227416739344347549899 61506341125109016521324849)
            ·
              refine ⟨46129755843831762390993637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61506341125109016521324849 46129755843831762390993637)
              ·
                refine ⟨8649329220718455448311307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46129755843831762390993637 8649329220718455448311307)
                ·
                  refine ⟨12973993831077683172466961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8649329220718455448311307 12973993831077683172466961)
                  ·
                    refine ⟨9730495373308262379350221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12973993831077683172466961 9730495373308262379350221)
                    ·
                      refine ⟨3648935764990598392256333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9730495373308262379350221 3648935764990598392256333)
                      ·
                        rfl

theorem cell23_7106277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_7106277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7106277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7106277 prefixEnd_7106277 := by exact prefixLift 7106277
  have htrace : WordTrace (prefixWord ++ tailWord_7106277) baseStart_7106277 baseEnd_7106277 := by
    simpa [prefixWord, tailWord_7106277, baseEnd_7106277] using wordTrace_append hprefix tailTrace_7106277
  have hstable : (prefixWord ++ tailWord_7106277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7106277).length < 2 ^ (prefixWord ++ tailWord_7106277).sum := by decide
  have hdescent : baseEnd_7106277 < baseStart_7106277 := by decide
  rcases family_descends (prefixWord ++ tailWord_7106277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7106294 : List Nat := [5, 1, 1, 1, 1, 4, 1, 3, 1, 2, 3]
def baseStart_7106294 : Nat := 118140960795 + 7106294 * 2 ^ 59
def prefixEnd_7106294 : Nat := 4983230072969 + 3 ^ 40 * 7106294 * 2
def baseEnd_7106294 : Nat := 3648944494161724825743755

theorem tailTrace_7106294 : CollatzResearch.WordTrace tailWord_7106294 prefixEnd_7106294 3648944494161724825743755 := by
  unfold tailWord_7106294
  simp only [CollatzResearch.WordTrace]
  refine ⟨16199239707319873202251871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 172791890211411980824019957 16199239707319873202251871)
  ·
    refine ⟨24298859560979809803377807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16199239707319873202251871 24298859560979809803377807)
    ·
      refine ⟨36448289341469714705066711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24298859560979809803377807 36448289341469714705066711)
      ·
        refine ⟨54672434012204572057600067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36448289341469714705066711 54672434012204572057600067)
        ·
          refine ⟨82008651018306858086400101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54672434012204572057600067 82008651018306858086400101)
          ·
            refine ⟨15376622065932535891200019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82008651018306858086400101 15376622065932535891200019)
            ·
              refine ⟨23064933098898803836800029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15376622065932535891200019 23064933098898803836800029)
              ·
                refine ⟨8649349912087051438800011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23064933098898803836800029 8649349912087051438800011)
                ·
                  refine ⟨12974024868130577158200017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8649349912087051438800011 12974024868130577158200017)
                  ·
                    refine ⟨9730518651097932868650013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12974024868130577158200017 9730518651097932868650013)
                    ·
                      refine ⟨3648944494161724825743755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9730518651097932868650013 3648944494161724825743755)
                      ·
                        rfl

theorem cell23_7106294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 3, 1, 2, 3].length) (baseStart_7106294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7106294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7106294 prefixEnd_7106294 := by exact prefixLift 7106294
  have htrace : WordTrace (prefixWord ++ tailWord_7106294) baseStart_7106294 baseEnd_7106294 := by
    simpa [prefixWord, tailWord_7106294, baseEnd_7106294] using wordTrace_append hprefix tailTrace_7106294
  have hstable : (prefixWord ++ tailWord_7106294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7106294).length < 2 ^ (prefixWord ++ tailWord_7106294).sum := by decide
  have hdescent : baseEnd_7106294 < baseStart_7106294 := by decide
  rcases family_descends (prefixWord ++ tailWord_7106294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7106323 : List Nat := [1, 1, 1, 2, 1, 3, 2, 3, 1, 8]
def baseStart_7106323 : Nat := 118140960795 + 7106323 * 2 ^ 59
def prefixEnd_7106323 : Nat := 4983230072969 + 3 ^ 40 * 7106323 * 2
def baseEnd_7106323 : Nat := 1216319795033568404093707

theorem tailTrace_7106323 : CollatzResearch.WordTrace tailWord_7106323 prefixEnd_7106323 1216319795033568404093707 := by
  unfold tailWord_7106323
  simp only [CollatzResearch.WordTrace]
  refine ⟨259188893034012909188835623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172792595356008606125890415 259188893034012909188835623)
  ·
    refine ⟨388783339551019363783253435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259188893034012909188835623 388783339551019363783253435)
    ·
      refine ⟨583175009326529045674880153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388783339551019363783253435 583175009326529045674880153)
      ·
        refine ⟨437381256994896784256160115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 583175009326529045674880153 437381256994896784256160115)
        ·
          refine ⟨656071885492345176384240173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 437381256994896784256160115 656071885492345176384240173)
          ·
            refine ⟨246026957059629441144090065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 656071885492345176384240173 246026957059629441144090065)
            ·
              refine ⟨184520217794722080858067549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246026957059629441144090065 184520217794722080858067549)
              ·
                refine ⟨69195081673020780321775331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 184520217794722080858067549 69195081673020780321775331)
                ·
                  refine ⟨103792622509531170482662997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69195081673020780321775331 103792622509531170482662997)
                  ·
                    refine ⟨1216319795033568404093707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 103792622509531170482662997 1216319795033568404093707)
                    ·
                      rfl

theorem cell23_7106323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 8].length) (baseStart_7106323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7106323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7106323 prefixEnd_7106323 := by exact prefixLift 7106323
  have htrace : WordTrace (prefixWord ++ tailWord_7106323) baseStart_7106323 baseEnd_7106323 := by
    simpa [prefixWord, tailWord_7106323, baseEnd_7106323] using wordTrace_append hprefix tailTrace_7106323
  have hstable : (prefixWord ++ tailWord_7106323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7106323).length < 2 ^ (prefixWord ++ tailWord_7106323).sum := by decide
  have hdescent : baseEnd_7106323 < baseStart_7106323 := by decide
  rcases family_descends (prefixWord ++ tailWord_7106323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7106364 : List Nat := [2, 2, 2, 2, 1, 1, 4, 1, 4, 2, 2]
def baseStart_7106364 : Nat := 118140960795 + 7106364 * 2 ^ 59
def prefixEnd_7106364 : Nat := 4983230072969 + 3 ^ 40 * 7106364 * 2
def baseEnd_7106364 : Nat := 3648980437807539551868433

theorem tailTrace_7106364 : CollatzResearch.WordTrace tailWord_7106364 prefixEnd_7106364 3648980437807539551868433 := by
  unfold tailWord_7106364
  simp only [CollatzResearch.WordTrace]
  refine ⟨129595194213432186595539073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172793592284576248794052097 129595194213432186595539073)
  ·
    refine ⟨97196395660074139946654305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129595194213432186595539073 97196395660074139946654305)
    ·
      refine ⟨72897296745055604959990729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97196395660074139946654305 72897296745055604959990729)
      ·
        refine ⟨54672972558791703719993047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72897296745055604959990729 54672972558791703719993047)
        ·
          refine ⟨82009458838187555579989571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54672972558791703719993047 82009458838187555579989571)
          ·
            refine ⟨123014188257281333369984357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82009458838187555579989571 123014188257281333369984357)
            ·
              refine ⟨23065160298240250006872067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123014188257281333369984357 23065160298240250006872067)
              ·
                refine ⟨34597740447360375010308101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23065160298240250006872067 34597740447360375010308101)
                ·
                  refine ⟨6487076333880070314432769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34597740447360375010308101 6487076333880070314432769)
                  ·
                    refine ⟨4865307250410052735824577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6487076333880070314432769 4865307250410052735824577)
                    ·
                      refine ⟨3648980437807539551868433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4865307250410052735824577 3648980437807539551868433)
                      ·
                        rfl

theorem cell23_7106364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 4, 2, 2].length) (baseStart_7106364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7106364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7106364 prefixEnd_7106364 := by exact prefixLift 7106364
  have htrace : WordTrace (prefixWord ++ tailWord_7106364) baseStart_7106364 baseEnd_7106364 := by
    simpa [prefixWord, tailWord_7106364, baseEnd_7106364] using wordTrace_append hprefix tailTrace_7106364
  have hstable : (prefixWord ++ tailWord_7106364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7106364).length < 2 ^ (prefixWord ++ tailWord_7106364).sum := by decide
  have hdescent : baseEnd_7106364 < baseStart_7106364 := by decide
  rcases family_descends (prefixWord ++ tailWord_7106364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7106481 : List Nat := [1, 2, 2, 4, 2, 1, 2, 4, 1, 4]
def baseStart_7106481 : Nat := 118140960795 + 7106481 * 2 ^ 59
def prefixEnd_7106481 : Nat := 4983230072969 + 3 ^ 40 * 7106481 * 2
def baseEnd_7106481 : Nat := 1216346838348038531368465

theorem tailTrace_7106481 : CollatzResearch.WordTrace tailWord_7106481 prefixEnd_7106481 1216346838348038531368465 := by
  unfold tailWord_7106481
  simp only [CollatzResearch.WordTrace]
  refine ⟨259194655767440502173087297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172796437178293668115391531 259194655767440502173087297)
  ·
    refine ⟨194395991825580376629815473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259194655767440502173087297 194395991825580376629815473)
    ·
      refine ⟨145796993869185282472361605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194395991825580376629815473 145796993869185282472361605)
      ·
        refine ⟨27336936350472240463567801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145796993869185282472361605 27336936350472240463567801)
        ·
          refine ⟨20502702262854180347675851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27336936350472240463567801 20502702262854180347675851)
          ·
            refine ⟨30754053394281270521513777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20502702262854180347675851 30754053394281270521513777)
            ·
              refine ⟨23065540045710952891135333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30754053394281270521513777 23065540045710952891135333)
              ·
                refine ⟨4324788758570803667087875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23065540045710952891135333 4324788758570803667087875)
                ·
                  refine ⟨6487183137856205500631813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4324788758570803667087875 6487183137856205500631813)
                  ·
                    refine ⟨1216346838348038531368465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6487183137856205500631813 1216346838348038531368465)
                    ·
                      rfl

theorem cell23_7106481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 4, 1, 4].length) (baseStart_7106481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7106481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7106481 prefixEnd_7106481 := by exact prefixLift 7106481
  have htrace : WordTrace (prefixWord ++ tailWord_7106481) baseStart_7106481 baseEnd_7106481 := by
    simpa [prefixWord, tailWord_7106481, baseEnd_7106481] using wordTrace_append hprefix tailTrace_7106481
  have hstable : (prefixWord ++ tailWord_7106481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7106481).length < 2 ^ (prefixWord ++ tailWord_7106481).sum := by decide
  have hdescent : baseEnd_7106481 < baseStart_7106481 := by decide
  rcases family_descends (prefixWord ++ tailWord_7106481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7106490 : List Nat := [3, 1, 1, 1, 2, 1, 2, 1, 2, 9]
def baseStart_7106490 : Nat := 118140960795 + 7106490 * 2 ^ 59
def prefixEnd_7106490 : Nat := 4983230072969 + 3 ^ 40 * 7106490 * 2
def baseEnd_7106490 : Nat := 1216348378790002019630951

theorem tailTrace_7106490 : CollatzResearch.WordTrace tailWord_7106490 prefixEnd_7106490 1216348378790002019630951 := by
  unfold tailWord_7106490
  simp only [CollatzResearch.WordTrace]
  refine ⟨64798746006101974177541231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172796656016271931140109949 64798746006101974177541231)
  ·
    refine ⟨97198119009152961266311847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64798746006101974177541231 97198119009152961266311847)
    ·
      refine ⟨145797178513729441899467771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97198119009152961266311847 145797178513729441899467771)
      ·
        refine ⟨218695767770594162849201657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145797178513729441899467771 218695767770594162849201657)
        ·
          refine ⟨164021825827945622136901243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218695767770594162849201657 164021825827945622136901243)
          ·
            refine ⟨246032738741918433205351865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164021825827945622136901243 246032738741918433205351865)
            ·
              refine ⟨184524554056438824904013899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246032738741918433205351865 184524554056438824904013899)
              ·
                refine ⟨276786831084658237356020849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184524554056438824904013899 276786831084658237356020849)
                ·
                  refine ⟨207590123313493678017015637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 276786831084658237356020849 207590123313493678017015637)
                  ·
                    refine ⟨1216348378790002019630951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 207590123313493678017015637 1216348378790002019630951)
                    ·
                      rfl

theorem cell23_7106490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 2, 9].length) (baseStart_7106490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7106490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7106490 prefixEnd_7106490 := by exact prefixLift 7106490
  have htrace : WordTrace (prefixWord ++ tailWord_7106490) baseStart_7106490 baseEnd_7106490 := by
    simpa [prefixWord, tailWord_7106490, baseEnd_7106490] using wordTrace_append hprefix tailTrace_7106490
  have hstable : (prefixWord ++ tailWord_7106490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7106490).length < 2 ^ (prefixWord ++ tailWord_7106490).sum := by decide
  have hdescent : baseEnd_7106490 < baseStart_7106490 := by decide
  rcases family_descends (prefixWord ++ tailWord_7106490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7106531 : List Nat := [1, 1, 1, 6, 1, 3, 1, 2, 2, 3, 2]
def baseStart_7106531 : Nat := 118140960795 + 7106531 * 2 ^ 59
def prefixEnd_7106531 : Nat := 4983230072969 + 3 ^ 40 * 7106531 * 2
def baseEnd_7106531 : Nat := 3649066189076840398480165

theorem tailTrace_7106531 : CollatzResearch.WordTrace tailWord_7106531 prefixEnd_7106531 3649066189076840398480165 := by
  unfold tailWord_7106531
  simp only [CollatzResearch.WordTrace]
  refine ⟨259196479417259360712407447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172797652944839573808271631 259196479417259360712407447)
  ·
    refine ⟨388794719125889041068611171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259196479417259360712407447 388794719125889041068611171)
    ·
      refine ⟨583192078688833561602916757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388794719125889041068611171 583192078688833561602916757)
      ·
        refine ⟨27337128688539073200136723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 583192078688833561602916757 27337128688539073200136723)
        ·
          refine ⟨41005693032808609800205085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27337128688539073200136723 41005693032808609800205085)
          ·
            refine ⟨15377134887303228675076907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41005693032808609800205085 15377134887303228675076907)
            ·
              refine ⟨23065702330954843012615361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15377134887303228675076907 23065702330954843012615361)
              ·
                refine ⟨17299276748216132259461521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23065702330954843012615361 17299276748216132259461521)
                ·
                  refine ⟨12974457561162099194596141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17299276748216132259461521 12974457561162099194596141)
                  ·
                    refine ⟨4865421585435787197973553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12974457561162099194596141 4865421585435787197973553)
                    ·
                      refine ⟨3649066189076840398480165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4865421585435787197973553 3649066189076840398480165)
                      ·
                        rfl

theorem cell23_7106531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 2, 2, 3, 2].length) (baseStart_7106531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7106531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7106531 prefixEnd_7106531 := by exact prefixLift 7106531
  have htrace : WordTrace (prefixWord ++ tailWord_7106531) baseStart_7106531 baseEnd_7106531 := by
    simpa [prefixWord, tailWord_7106531, baseEnd_7106531] using wordTrace_append hprefix tailTrace_7106531
  have hstable : (prefixWord ++ tailWord_7106531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7106531).length < 2 ^ (prefixWord ++ tailWord_7106531).sum := by decide
  have hdescent : baseEnd_7106531 < baseStart_7106531 := by decide
  rcases family_descends (prefixWord ++ tailWord_7106531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7106557 : List Nat := [1, 4, 1, 1, 1, 2, 4, 1, 1, 1, 6]
def baseStart_7106557 : Nat := 118140960795 + 7106557 * 2 ^ 59
def prefixEnd_7106557 : Nat := 4983230072969 + 3 ^ 40 * 7106557 * 2
def baseEnd_7106557 : Nat := 3649079539573857296755045

theorem tailTrace_7106557 : CollatzResearch.WordTrace tailWord_7106557 prefixEnd_7106557 3649079539573857296755045 := by
  unfold tailWord_7106557
  simp only [CollatzResearch.WordTrace]
  refine ⟨259197427715165167152853925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172798285143443444768569283 259197427715165167152853925)
  ·
    refine ⟨48599517696593468841160111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 259197427715165167152853925 48599517696593468841160111)
    ·
      refine ⟨72899276544890203261740167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48599517696593468841160111 72899276544890203261740167)
      ·
        refine ⟨109348914817335304892610251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72899276544890203261740167 109348914817335304892610251)
        ·
          refine ⟨164023372226002957338915377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109348914817335304892610251 164023372226002957338915377)
          ·
            refine ⟨123017529169502218004186533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164023372226002957338915377 123017529169502218004186533)
            ·
              refine ⟨23065786719281665875784975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123017529169502218004186533 23065786719281665875784975)
              ·
                refine ⟨34598680078922498813677463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23065786719281665875784975 34598680078922498813677463)
                ·
                  refine ⟨51898020118383748220516195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34598680078922498813677463 51898020118383748220516195)
                  ·
                    refine ⟨77847030177575622330774293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51898020118383748220516195 77847030177575622330774293)
                    ·
                      refine ⟨3649079539573857296755045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77847030177575622330774293 3649079539573857296755045)
                      ·
                        rfl

theorem cell23_7106557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 1, 6].length) (baseStart_7106557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7106557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7106557 prefixEnd_7106557 := by exact prefixLift 7106557
  have htrace : WordTrace (prefixWord ++ tailWord_7106557) baseStart_7106557 baseEnd_7106557 := by
    simpa [prefixWord, tailWord_7106557, baseEnd_7106557] using wordTrace_append hprefix tailTrace_7106557
  have hstable : (prefixWord ++ tailWord_7106557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7106557).length < 2 ^ (prefixWord ++ tailWord_7106557).sum := by decide
  have hdescent : baseEnd_7106557 < baseStart_7106557 := by decide
  rcases family_descends (prefixWord ++ tailWord_7106557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7106558 : List Nat := [4, 2, 2, 2, 1, 3, 1, 2, 1, 5]
def baseStart_7106558 : Nat := 118140960795 + 7106558 * 2 ^ 59
def prefixEnd_7106558 : Nat := 4983230072969 + 3 ^ 40 * 7106558 * 2
def baseEnd_7106558 : Nat := 1216360017684837264280847

theorem tailTrace_7106558 : CollatzResearch.WordTrace tailWord_7106558 prefixEnd_7106558 1216360017684837264280847 := by
  unfold tailWord_7106558
  simp only [CollatzResearch.WordTrace]
  refine ⟨32399683023520193040455041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172798309458774362882426885 32399683023520193040455041)
  ·
    refine ⟨24299762267640144780341281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32399683023520193040455041 24299762267640144780341281)
    ·
      refine ⟨18224821700730108585255961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24299762267640144780341281 18224821700730108585255961)
      ·
        refine ⟨13668616275547581438941971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18224821700730108585255961 13668616275547581438941971)
        ·
          refine ⟨20502924413321372158412957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13668616275547581438941971 20502924413321372158412957)
          ·
            refine ⟨7688596654995514559404859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20502924413321372158412957 7688596654995514559404859)
            ·
              refine ⟨11532894982493271839107289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7688596654995514559404859 11532894982493271839107289)
              ·
                refine ⟨8649671236869953879330467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11532894982493271839107289 8649671236869953879330467)
                ·
                  refine ⟨12974506855304930818995701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8649671236869953879330467 12974506855304930818995701)
                  ·
                    refine ⟨1216360017684837264280847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12974506855304930818995701 1216360017684837264280847)
                    ·
                      rfl

theorem cell23_7106558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_7106558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7106558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7106558 prefixEnd_7106558 := by exact prefixLift 7106558
  have htrace : WordTrace (prefixWord ++ tailWord_7106558) baseStart_7106558 baseEnd_7106558 := by
    simpa [prefixWord, tailWord_7106558, baseEnd_7106558] using wordTrace_append hprefix tailTrace_7106558
  have hstable : (prefixWord ++ tailWord_7106558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7106558).length < 2 ^ (prefixWord ++ tailWord_7106558).sum := by decide
  have hdescent : baseEnd_7106558 < baseStart_7106558 := by decide
  rcases family_descends (prefixWord ++ tailWord_7106558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7106561 : List Nat := [1, 2, 4, 1, 2, 1, 2, 1, 5, 2, 2]
def baseStart_7106561 : Nat := 118140960795 + 7106561 * 2 ^ 59
def prefixEnd_7106561 : Nat := 4983230072969 + 3 ^ 40 * 7106561 * 2
def baseEnd_7106561 : Nat := 3649081593496475281105027

theorem tailTrace_7106561 : CollatzResearch.WordTrace tailWord_7106561 prefixEnd_7106561 3649081593496475281105027 := by
  unfold tailWord_7106561
  simp only [CollatzResearch.WordTrace]
  refine ⟨259197573607150675835999537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172798382404767117223999691 259197573607150675835999537)
  ·
    refine ⟨194398180205363006876999653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259197573607150675835999537 194398180205363006876999653)
    ·
      refine ⟨36449658788505563789437435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 194398180205363006876999653 36449658788505563789437435)
      ·
        refine ⟨54674488182758345684156153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36449658788505563789437435 54674488182758345684156153)
        ·
          refine ⟨41005866137068759263117115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54674488182758345684156153 41005866137068759263117115)
          ·
            refine ⟨61508799205603138894675673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41005866137068759263117115 61508799205603138894675673)
            ·
              refine ⟨46131599404202354171006755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61508799205603138894675673 46131599404202354171006755)
              ·
                refine ⟨69197399106303531256510133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46131599404202354171006755 69197399106303531256510133)
                ·
                  refine ⟨6487256166215956055297825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69197399106303531256510133 6487256166215956055297825)
                  ·
                    refine ⟨4865442124661967041473369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6487256166215956055297825 4865442124661967041473369)
                    ·
                      refine ⟨3649081593496475281105027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4865442124661967041473369 3649081593496475281105027)
                      ·
                        rfl

theorem cell23_7106561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 5, 2, 2].length) (baseStart_7106561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7106561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7106561 prefixEnd_7106561 := by exact prefixLift 7106561
  have htrace : WordTrace (prefixWord ++ tailWord_7106561) baseStart_7106561 baseEnd_7106561 := by
    simpa [prefixWord, tailWord_7106561, baseEnd_7106561] using wordTrace_append hprefix tailTrace_7106561
  have hstable : (prefixWord ++ tailWord_7106561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7106561).length < 2 ^ (prefixWord ++ tailWord_7106561).sum := by decide
  have hdescent : baseEnd_7106561 < baseStart_7106561 := by decide
  rcases family_descends (prefixWord ++ tailWord_7106561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7106567 : List Nat := [1, 1, 4, 3, 1, 2, 2, 9]
def baseStart_7106567 : Nat := 118140960795 + 7106567 * 2 ^ 59
def prefixEnd_7106567 : Nat := 4983230072969 + 3 ^ 40 * 7106567 * 2
def baseEnd_7106567 : Nat := 135151284236311194727037

theorem tailTrace_7106567 : CollatzResearch.WordTrace tailWord_7106567 prefixEnd_7106567 135151284236311194727037 := by
  unfold tailWord_7106567
  simp only [CollatzResearch.WordTrace]
  refine ⟨259197792445128938860717955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172798528296752625907145303 259197792445128938860717955)
  ·
    refine ⟨388796688667693408291076933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259197792445128938860717955 388796688667693408291076933)
    ·
      refine ⟨72899379125192514054576925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 388796688667693408291076933 72899379125192514054576925)
      ·
        refine ⟨27337267171947192770466347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72899379125192514054576925 27337267171947192770466347)
        ·
          refine ⟨41005900757920789155699521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27337267171947192770466347 41005900757920789155699521)
          ·
            refine ⟨30754425568440591866774641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41005900757920789155699521 30754425568440591866774641)
            ·
              refine ⟨23065819176330443900080981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30754425568440591866774641 23065819176330443900080981)
              ·
                refine ⟨135151284236311194727037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23065819176330443900080981 135151284236311194727037)
                ·
                  rfl

theorem cell23_7106567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 9].length) (baseStart_7106567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7106567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7106567 prefixEnd_7106567 := by exact prefixLift 7106567
  have htrace : WordTrace (prefixWord ++ tailWord_7106567) baseStart_7106567 baseEnd_7106567 := by
    simpa [prefixWord, tailWord_7106567, baseEnd_7106567] using wordTrace_append hprefix tailTrace_7106567
  have hstable : (prefixWord ++ tailWord_7106567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7106567).length < 2 ^ (prefixWord ++ tailWord_7106567).sum := by decide
  have hdescent : baseEnd_7106567 < baseStart_7106567 := by decide
  rcases family_descends (prefixWord ++ tailWord_7106567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7106574 : List Nat := [4, 1, 1, 2, 2, 1, 3, 2, 1, 2, 4]
def baseStart_7106574 : Nat := 118140960795 + 7106574 * 2 ^ 59
def prefixEnd_7106574 : Nat := 4983230072969 + 3 ^ 40 * 7106574 * 2
def baseEnd_7106574 : Nat := 3649088268744983730242467

theorem tailTrace_7106574 : CollatzResearch.WordTrace tailWord_7106574 prefixEnd_7106574 3649088268744983730242467 := by
  unfold tailWord_7106574
  simp only [CollatzResearch.WordTrace]
  refine ⟨32399755969512947382027847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172798698504069052704148517 32399755969512947382027847)
  ·
    refine ⟨48599633954269421073041771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32399755969512947382027847 48599633954269421073041771)
    ·
      refine ⟨72899450931404131609562657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48599633954269421073041771 72899450931404131609562657)
      ·
        refine ⟨54674588198553098707171993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72899450931404131609562657 54674588198553098707171993)
        ·
          refine ⟨41005941148914824030378995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54674588198553098707171993 41005941148914824030378995)
          ·
            refine ⟨61508911723372236045568493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41005941148914824030378995 61508911723372236045568493)
            ·
              refine ⟨23065841896264588517088185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61508911723372236045568493 23065841896264588517088185)
              ·
                refine ⟨17299381422198441387816139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23065841896264588517088185 17299381422198441387816139)
                ·
                  refine ⟨25949072133297662081724209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17299381422198441387816139 25949072133297662081724209)
                  ·
                    refine ⟨19461804099973246561293157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25949072133297662081724209 19461804099973246561293157)
                    ·
                      refine ⟨3649088268744983730242467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19461804099973246561293157 3649088268744983730242467)
                      ·
                        rfl

theorem cell23_7106574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_7106574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7106574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7106574 prefixEnd_7106574 := by exact prefixLift 7106574
  have htrace : WordTrace (prefixWord ++ tailWord_7106574) baseStart_7106574 baseEnd_7106574 := by
    simpa [prefixWord, tailWord_7106574, baseEnd_7106574] using wordTrace_append hprefix tailTrace_7106574
  have hstable : (prefixWord ++ tailWord_7106574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7106574).length < 2 ^ (prefixWord ++ tailWord_7106574).sum := by decide
  have hdescent : baseEnd_7106574 < baseStart_7106574 := by decide
  rcases family_descends (prefixWord ++ tailWord_7106574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7106581 : List Nat := [1, 3, 2, 1, 5, 2, 1, 1, 1, 1, 5]
def baseStart_7106581 : Nat := 118140960795 + 7106581 * 2 ^ 59
def prefixEnd_7106581 : Nat := 4983230072969 + 3 ^ 40 * 7106581 * 2
def baseEnd_7106581 : Nat := 3649091863109565202854935

theorem tailTrace_7106581 : CollatzResearch.WordTrace tailWord_7106581 prefixEnd_7106581 3649091863109565202854935 := by
  unfold tailWord_7106581
  simp only [CollatzResearch.WordTrace]
  refine ⟨259198303067078219251727597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172798868711385479501151731 259198303067078219251727597)
  ·
    refine ⟨97199363650154332219397849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259198303067078219251727597 97199363650154332219397849)
    ·
      refine ⟨72899522737615749164548387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97199363650154332219397849 72899522737615749164548387)
      ·
        refine ⟨109349284106423623746822581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72899522737615749164548387 109349284106423623746822581)
        ·
          refine ⟨10251495384977214726264617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 109349284106423623746822581 10251495384977214726264617)
          ·
            refine ⟨7688621538732911044698463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10251495384977214726264617 7688621538732911044698463)
            ·
              refine ⟨11532932308099366567047695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7688621538732911044698463 11532932308099366567047695)
              ·
                refine ⟨17299398462149049850571543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11532932308099366567047695 17299398462149049850571543)
                ·
                  refine ⟨25949097693223574775857315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17299398462149049850571543 25949097693223574775857315)
                  ·
                    refine ⟨38923646539835362163785973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25949097693223574775857315 38923646539835362163785973)
                    ·
                      refine ⟨3649091863109565202854935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38923646539835362163785973 3649091863109565202854935)
                      ·
                        rfl

theorem cell23_7106581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 1, 1, 1, 5].length) (baseStart_7106581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7106581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7106581 prefixEnd_7106581 := by exact prefixLift 7106581
  have htrace : WordTrace (prefixWord ++ tailWord_7106581) baseStart_7106581 baseEnd_7106581 := by
    simpa [prefixWord, tailWord_7106581, baseEnd_7106581] using wordTrace_append hprefix tailTrace_7106581
  have hstable : (prefixWord ++ tailWord_7106581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7106581).length < 2 ^ (prefixWord ++ tailWord_7106581).sum := by decide
  have hdescent : baseEnd_7106581 < baseStart_7106581 := by decide
  rcases family_descends (prefixWord ++ tailWord_7106581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7106594 : List Nat := [3, 3, 1, 1, 1, 2, 1, 2, 3, 3, 3]
def baseStart_7106594 : Nat := 118140960795 + 7106594 * 2 ^ 59
def prefixEnd_7106594 : Nat := 4983230072969 + 3 ^ 40 * 7106594 * 2
def baseEnd_7106594 : Nat := 3649098538358073651992375

theorem tailTrace_7106594 : CollatzResearch.WordTrace tailWord_7106594 prefixEnd_7106594 3649098538358073651992375 := by
  unfold tailWord_7106594
  simp only [CollatzResearch.WordTrace]
  refine ⟨64799694304007780617987709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172799184810687414981300557 64799694304007780617987709)
  ·
    refine ⟨24299885364002917731745391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64799694304007780617987709 24299885364002917731745391)
    ·
      refine ⟨36449828046004376597618087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24299885364002917731745391 36449828046004376597618087)
      ·
        refine ⟨54674742069006564896427131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36449828046004376597618087 54674742069006564896427131)
        ·
          refine ⟨82012113103509847344640697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54674742069006564896427131 82012113103509847344640697)
          ·
            refine ⟨61509084827632385508480523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82012113103509847344640697 61509084827632385508480523)
            ·
              refine ⟨92263627241448578262720785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61509084827632385508480523 92263627241448578262720785)
              ·
                refine ⟨69197720431086433697040589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92263627241448578262720785 69197720431086433697040589)
                ·
                  refine ⟨25949145161657412636390221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69197720431086433697040589 25949145161657412636390221)
                  ·
                    refine ⟨9730929435621529738646333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25949145161657412636390221 9730929435621529738646333)
                    ·
                      refine ⟨3649098538358073651992375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9730929435621529738646333 3649098538358073651992375)
                      ·
                        rfl

theorem cell23_7106594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 3, 3, 3].length) (baseStart_7106594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7106594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7106594 prefixEnd_7106594 := by exact prefixLift 7106594
  have htrace : WordTrace (prefixWord ++ tailWord_7106594) baseStart_7106594 baseEnd_7106594 := by
    simpa [prefixWord, tailWord_7106594, baseEnd_7106594] using wordTrace_append hprefix tailTrace_7106594
  have hstable : (prefixWord ++ tailWord_7106594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7106594).length < 2 ^ (prefixWord ++ tailWord_7106594).sum := by decide
  have hdescent : baseEnd_7106594 < baseStart_7106594 := by decide
  rcases family_descends (prefixWord ++ tailWord_7106594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7106597 : List Nat := [1, 3, 1, 2, 2, 3, 1, 1, 2, 7]
def baseStart_7106597 : Nat := 118140960795 + 7106597 * 2 ^ 59
def prefixEnd_7106597 : Nat := 4983230072969 + 3 ^ 40 * 7106597 * 2
def baseEnd_7106597 : Nat := 1216366692933345713418287

theorem tailTrace_7106597 : CollatzResearch.WordTrace tailWord_7106597 prefixEnd_7106597 1216366692933345713418287 := by
  unfold tailWord_7106597
  simp only [CollatzResearch.WordTrace]
  refine ⟨259198886635020253984310045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172799257756680169322873363 259198886635020253984310045)
  ·
    refine ⟨97199582488132595244116267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259198886635020253984310045 97199582488132595244116267)
    ·
      refine ⟨145799373732198892866174401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97199582488132595244116267 145799373732198892866174401)
      ·
        refine ⟨109349530299149169649630801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145799373732198892866174401 109349530299149169649630801)
        ·
          refine ⟨82012147724361877237223101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109349530299149169649630801 82012147724361877237223101)
          ·
            refine ⟨30754555396635703963958663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82012147724361877237223101 30754555396635703963958663)
            ·
              refine ⟨46131833094953555945937995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30754555396635703963958663 46131833094953555945937995)
              ·
                refine ⟨69197749642430333918906993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46131833094953555945937995 69197749642430333918906993)
                ·
                  refine ⟨51898312231822750439180245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69197749642430333918906993 51898312231822750439180245)
                  ·
                    refine ⟨1216366692933345713418287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51898312231822750439180245 1216366692933345713418287)
                    ·
                      rfl

theorem cell23_7106597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 7].length) (baseStart_7106597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7106597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7106597 prefixEnd_7106597 := by exact prefixLift 7106597
  have htrace : WordTrace (prefixWord ++ tailWord_7106597) baseStart_7106597 baseEnd_7106597 := by
    simpa [prefixWord, tailWord_7106597, baseEnd_7106597] using wordTrace_append hprefix tailTrace_7106597
  have hstable : (prefixWord ++ tailWord_7106597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7106597).length < 2 ^ (prefixWord ++ tailWord_7106597).sum := by decide
  have hdescent : baseEnd_7106597 < baseStart_7106597 := by decide
  rcases family_descends (prefixWord ++ tailWord_7106597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7106611 : List Nat := [1, 1, 1, 2, 4, 1, 4, 3, 2, 1, 3]
def baseStart_7106611 : Nat := 118140960795 + 7106611 * 2 ^ 59
def prefixEnd_7106611 : Nat := 4983230072969 + 3 ^ 40 * 7106611 * 2
def baseEnd_7106611 : Nat := 3649107267529200085479797

theorem tailTrace_7106611 : CollatzResearch.WordTrace tailWord_7106611 prefixEnd_7106611 3649107267529200085479797 := by
  unfold tailWord_7106611
  simp only [CollatzResearch.WordTrace]
  refine ⟨259199397256969534375319687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172799598171313022916879791 259199397256969534375319687)
  ·
    refine ⟨388799095885454301562979531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259199397256969534375319687 388799095885454301562979531)
    ·
      refine ⟨583198643828181452344469297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388799095885454301562979531 583198643828181452344469297)
      ·
        refine ⟨437398982871136089258351973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 583198643828181452344469297 437398982871136089258351973)
        ·
          refine ⟨82012309288338016735940995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 437398982871136089258351973 82012309288338016735940995)
          ·
            refine ⟨123018463932507025103911493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82012309288338016735940995 123018463932507025103911493)
            ·
              refine ⟨23065961987345067206983405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123018463932507025103911493 23065961987345067206983405)
              ·
                refine ⟨8649735745254400202618777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23065961987345067206983405 8649735745254400202618777)
                ·
                  refine ⟨6487301808940800151964083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8649735745254400202618777 6487301808940800151964083)
                  ·
                    refine ⟨9730952713411200227946125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6487301808940800151964083 9730952713411200227946125)
                    ·
                      refine ⟨3649107267529200085479797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9730952713411200227946125 3649107267529200085479797)
                      ·
                        rfl

theorem cell23_7106611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 3, 2, 1, 3].length) (baseStart_7106611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7106611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7106611 prefixEnd_7106611 := by exact prefixLift 7106611
  have htrace : WordTrace (prefixWord ++ tailWord_7106611) baseStart_7106611 baseEnd_7106611 := by
    simpa [prefixWord, tailWord_7106611, baseEnd_7106611] using wordTrace_append hprefix tailTrace_7106611
  have hstable : (prefixWord ++ tailWord_7106611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7106611).length < 2 ^ (prefixWord ++ tailWord_7106611).sum := by decide
  have hdescent : baseEnd_7106611 < baseStart_7106611 := by decide
  rcases family_descends (prefixWord ++ tailWord_7106611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7106614 : List Nat := [5, 1, 2, 1, 1, 1, 1, 2, 2, 7]
def baseStart_7106614 : Nat := 118140960795 + 7106614 * 2 ^ 59
def prefixEnd_7106614 : Nat := 4983230072969 + 3 ^ 40 * 7106614 * 2
def baseEnd_7106614 : Nat := 1216369602657054524580761

theorem tailTrace_7106614 : CollatzResearch.WordTrace tailWord_7106614 prefixEnd_7106614 1216369602657054524580761 := by
  unfold tailWord_7106614
  simp only [CollatzResearch.WordTrace]
  refine ⟨16199969167247416617979931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 172799671117305777258452597 16199969167247416617979931)
  ·
    refine ⟨24299953750871124926969897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16199969167247416617979931 24299953750871124926969897)
    ·
      refine ⟨18224965313153343695227423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24299953750871124926969897 18224965313153343695227423)
      ·
        refine ⟨27337447969730015542841135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18224965313153343695227423 27337447969730015542841135)
        ·
          refine ⟨41006171954595023314261703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27337447969730015542841135 41006171954595023314261703)
          ·
            refine ⟨61509257931892534971392555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41006171954595023314261703 61509257931892534971392555)
            ·
              refine ⟨92263886897838802457088833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61509257931892534971392555 92263886897838802457088833)
              ·
                refine ⟨69197915173379101842816625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92263886897838802457088833 69197915173379101842816625)
                ·
                  refine ⟨51898436380034326382112469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69197915173379101842816625 51898436380034326382112469)
                  ·
                    refine ⟨1216369602657054524580761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51898436380034326382112469 1216369602657054524580761)
                    ·
                      rfl

theorem cell23_7106614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_7106614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7106614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7106614 prefixEnd_7106614 := by exact prefixLift 7106614
  have htrace : WordTrace (prefixWord ++ tailWord_7106614) baseStart_7106614 baseEnd_7106614 := by
    simpa [prefixWord, tailWord_7106614, baseEnd_7106614] using wordTrace_append hprefix tailTrace_7106614
  have hstable : (prefixWord ++ tailWord_7106614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7106614).length < 2 ^ (prefixWord ++ tailWord_7106614).sum := by decide
  have hdescent : baseEnd_7106614 < baseStart_7106614 := by decide
  rcases family_descends (prefixWord ++ tailWord_7106614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7106621 : List Nat := [1, 4, 1, 3, 1, 1, 1, 3, 3, 3, 2]
def baseStart_7106621 : Nat := 118140960795 + 7106621 * 2 ^ 59
def prefixEnd_7106621 : Nat := 4983230072969 + 3 ^ 40 * 7106621 * 2
def baseEnd_7106621 : Nat := 3649112402335745046354751

theorem tailTrace_7106621 : CollatzResearch.WordTrace tailWord_7106621 prefixEnd_7106621 3649112402335745046354751 := by
  unfold tailWord_7106621
  simp only [CollatzResearch.WordTrace]
  refine ⟨259199761986933306083183717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172799841324622204055455811 259199761986933306083183717)
  ·
    refine ⟨48599955372549994890596947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 259199761986933306083183717 48599955372549994890596947)
    ·
      refine ⟨72899933058824992335895421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48599955372549994890596947 72899933058824992335895421)
      ·
        refine ⟨27337474897059372125960783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72899933058824992335895421 27337474897059372125960783)
        ·
          refine ⟨41006212345589058188941175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27337474897059372125960783 41006212345589058188941175)
          ·
            refine ⟨61509318518383587283411763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41006212345589058188941175 61509318518383587283411763)
            ·
              refine ⟨92263977777575380925117645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61509318518383587283411763 92263977777575380925117645)
              ·
                refine ⟨34598991666590767846919117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92263977777575380925117645 34598991666590767846919117)
                ·
                  refine ⟨12974621874971537942594669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34598991666590767846919117 12974621874971537942594669)
                  ·
                    refine ⟨4865483203114326728473001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12974621874971537942594669 4865483203114326728473001)
                    ·
                      refine ⟨3649112402335745046354751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4865483203114326728473001 3649112402335745046354751)
                      ·
                        rfl

theorem cell23_7106621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 3, 3, 2].length) (baseStart_7106621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7106621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7106621 prefixEnd_7106621 := by exact prefixLift 7106621
  have htrace : WordTrace (prefixWord ++ tailWord_7106621) baseStart_7106621 baseEnd_7106621 := by
    simpa [prefixWord, tailWord_7106621, baseEnd_7106621] using wordTrace_append hprefix tailTrace_7106621
  have hstable : (prefixWord ++ tailWord_7106621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7106621).length < 2 ^ (prefixWord ++ tailWord_7106621).sum := by decide
  have hdescent : baseEnd_7106621 < baseStart_7106621 := by decide
  rcases family_descends (prefixWord ++ tailWord_7106621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7106638 : List Nat := [4, 1, 1, 1, 1, 5, 1, 3, 1, 3, 2]
def baseStart_7106638 : Nat := 118140960795 + 7106638 * 2 ^ 59
def prefixEnd_7106638 : Nat := 4983230072969 + 3 ^ 40 * 7106638 * 2
def baseEnd_7106638 : Nat := 3649121131506871479842173

theorem tailTrace_7106638 : CollatzResearch.WordTrace tailWord_7106638 prefixEnd_7106638 3649121131506871479842173 := by
  unfold tailWord_7106638
  simp only [CollatzResearch.WordTrace]
  refine ⟨32400047753483964748319071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172800254685247811991035045 32400047753483964748319071)
  ·
    refine ⟨48600071630225947122478607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32400047753483964748319071 48600071630225947122478607)
    ·
      refine ⟨72900107445338920683717911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48600071630225947122478607 72900107445338920683717911)
      ·
        refine ⟨109350161168008381025576867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72900107445338920683717911 109350161168008381025576867)
        ·
          refine ⟨164025241752012571538365301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109350161168008381025576867 164025241752012571538365301)
          ·
            refine ⟨15377366414251178581721747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 164025241752012571538365301 15377366414251178581721747)
            ·
              refine ⟨23066049621376767872582621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15377366414251178581721747 23066049621376767872582621)
              ·
                refine ⟨8649768608016287952218483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23066049621376767872582621 8649768608016287952218483)
                ·
                  refine ⟨12974652912024431928327725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8649768608016287952218483 12974652912024431928327725)
                  ·
                    refine ⟨4865494842009161973122897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12974652912024431928327725 4865494842009161973122897)
                    ·
                      refine ⟨3649121131506871479842173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4865494842009161973122897 3649121131506871479842173)
                      ·
                        rfl

theorem cell23_7106638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 3, 1, 3, 2].length) (baseStart_7106638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7106638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7106638 prefixEnd_7106638 := by exact prefixLift 7106638
  have htrace : WordTrace (prefixWord ++ tailWord_7106638) baseStart_7106638 baseEnd_7106638 := by
    simpa [prefixWord, tailWord_7106638, baseEnd_7106638] using wordTrace_append hprefix tailTrace_7106638
  have hstable : (prefixWord ++ tailWord_7106638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7106638).length < 2 ^ (prefixWord ++ tailWord_7106638).sum := by decide
  have hdescent : baseEnd_7106638 < baseStart_7106638 := by decide
  rcases family_descends (prefixWord ++ tailWord_7106638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7106668 : List Nat := [2, 2, 1, 1, 3, 5, 1, 1, 1, 4, 2]
def baseStart_7106668 : Nat := 118140960795 + 7106668 * 2 ^ 59
def prefixEnd_7106668 : Nat := 4983230072969 + 3 ^ 40 * 7106668 * 2
def baseEnd_7106668 : Nat := 3649136535926506362467035

theorem tailTrace_7106668 : CollatzResearch.WordTrace tailWord_7106668 prefixEnd_7106668 3649136535926506362467035 := by
  unfold tailWord_7106668
  simp only [CollatzResearch.WordTrace]
  refine ⟨129600738108881516555072329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172800984145175355406763105 129600738108881516555072329)
  ·
    refine ⟨97200553581661137416304247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129600738108881516555072329 97200553581661137416304247)
    ·
      refine ⟨145800830372491706124456371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97200553581661137416304247 145800830372491706124456371)
      ·
        refine ⟨218701245558737559186684557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145800830372491706124456371 218701245558737559186684557)
        ·
          refine ⟨82012967084526584695006709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218701245558737559186684557 82012967084526584695006709)
          ·
            refine ⟨7688715664174367315156879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82012967084526584695006709 7688715664174367315156879)
            ·
              refine ⟨11533073496261550972735319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7688715664174367315156879 11533073496261550972735319)
              ·
                refine ⟨17299610244392326459102979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11533073496261550972735319 17299610244392326459102979)
                ·
                  refine ⟨25949415366588489688654469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17299610244392326459102979 25949415366588489688654469)
                  ·
                    refine ⟨4865515381235341816622713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25949415366588489688654469 4865515381235341816622713)
                    ·
                      refine ⟨3649136535926506362467035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4865515381235341816622713 3649136535926506362467035)
                      ·
                        rfl

theorem cell23_7106668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 4, 2].length) (baseStart_7106668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7106668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7106668 prefixEnd_7106668 := by exact prefixLift 7106668
  have htrace : WordTrace (prefixWord ++ tailWord_7106668) baseStart_7106668 baseEnd_7106668 := by
    simpa [prefixWord, tailWord_7106668, baseEnd_7106668] using wordTrace_append hprefix tailTrace_7106668
  have hstable : (prefixWord ++ tailWord_7106668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7106668).length < 2 ^ (prefixWord ++ tailWord_7106668).sum := by decide
  have hdescent : baseEnd_7106668 < baseStart_7106668 := by decide
  rcases family_descends (prefixWord ++ tailWord_7106668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7106674 : List Nat := [3, 2, 1, 2, 2, 2, 2, 2, 7]
def baseStart_7106674 : Nat := 118140960795 + 7106674 * 2 ^ 59
def prefixEnd_7106674 : Nat := 4983230072969 + 3 ^ 40 * 7106674 * 2
def baseEnd_7106674 : Nat := 405459957423381482110223

theorem tailTrace_7106674 : CollatzResearch.WordTrace tailWord_7106674 prefixEnd_7106674 405459957423381482110223 := by
  unfold tailWord_7106674
  simp only [CollatzResearch.WordTrace]
  refine ⟨64800423763935324033715769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172801130037160864089908717 64800423763935324033715769)
  ·
    refine ⟨48600317822951493025286827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64800423763935324033715769 48600317822951493025286827)
    ·
      refine ⟨72900476734427239537930241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48600317822951493025286827 72900476734427239537930241)
      ·
        refine ⟨54675357550820429653447681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72900476734427239537930241 54675357550820429653447681)
        ·
          refine ⟨41006518163115322240085761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54675357550820429653447681 41006518163115322240085761)
          ·
            refine ⟨30754888622336491680064321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41006518163115322240085761 30754888622336491680064321)
            ·
              refine ⟨23066166466752368760048241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30754888622336491680064321 23066166466752368760048241)
              ·
                refine ⟨17299624850064276570036181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23066166466752368760048241 17299624850064276570036181)
                ·
                  refine ⟨405459957423381482110223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17299624850064276570036181 405459957423381482110223)
                  ·
                    rfl

theorem cell23_7106674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 2, 7].length) (baseStart_7106674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7106674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7106674 prefixEnd_7106674 := by exact prefixLift 7106674
  have htrace : WordTrace (prefixWord ++ tailWord_7106674) baseStart_7106674 baseEnd_7106674 := by
    simpa [prefixWord, tailWord_7106674, baseEnd_7106674] using wordTrace_append hprefix tailTrace_7106674
  have hstable : (prefixWord ++ tailWord_7106674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7106674).length < 2 ^ (prefixWord ++ tailWord_7106674).sum := by decide
  have hdescent : baseEnd_7106674 < baseStart_7106674 := by decide
  rcases family_descends (prefixWord ++ tailWord_7106674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7106691 : List Nat := [1, 1, 1, 3, 3, 3, 3, 3, 5]
def baseStart_7106691 : Nat := 118140960795 + 7106691 * 2 ^ 59
def prefixEnd_7106691 : Nat := 4983230072969 + 3 ^ 40 * 7106691 * 2
def baseEnd_7106691 : Nat := 405460927331284419164381

theorem tailTrace_7106691 : CollatzResearch.WordTrace tailWord_7106691 prefixEnd_7106691 405460927331284419164381 := by
  unfold tailWord_7106691
  simp only [CollatzResearch.WordTrace]
  refine ⟨259202315096679708038231927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172801543397786472025487951 259202315096679708038231927)
  ·
    refine ⟨388803472645019562057347891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259202315096679708038231927 388803472645019562057347891)
    ·
      refine ⟨583205208967529343086021837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388803472645019562057347891 583205208967529343086021837)
      ·
        refine ⟨218701953362823503657258189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 583205208967529343086021837 218701953362823503657258189)
        ·
          refine ⟨82013232511058813871471821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218701953362823503657258189 82013232511058813871471821)
          ·
            refine ⟨30754962191647055201801933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82013232511058813871471821 30754962191647055201801933)
            ·
              refine ⟨11533110821867645700675725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30754962191647055201801933 11533110821867645700675725)
              ·
                refine ⟨4324916558200367137753397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11533110821867645700675725 4324916558200367137753397)
                ·
                  refine ⟨405460927331284419164381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4324916558200367137753397 405460927331284419164381)
                  ·
                    rfl

theorem cell23_7106691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 3, 5].length) (baseStart_7106691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7106691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7106691 prefixEnd_7106691 := by exact prefixLift 7106691
  have htrace : WordTrace (prefixWord ++ tailWord_7106691) baseStart_7106691 baseEnd_7106691 := by
    simpa [prefixWord, tailWord_7106691, baseEnd_7106691] using wordTrace_append hprefix tailTrace_7106691
  have hstable : (prefixWord ++ tailWord_7106691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7106691).length < 2 ^ (prefixWord ++ tailWord_7106691).sum := by decide
  have hdescent : baseEnd_7106691 < baseStart_7106691 := by decide
  rcases family_descends (prefixWord ++ tailWord_7106691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7106704 : List Nat := [2, 1, 1, 1, 1, 1, 7, 2, 2, 5]
def baseStart_7106704 : Nat := 118140960795 + 7106704 * 2 ^ 59
def prefixEnd_7106704 : Nat := 4983230072969 + 3 ^ 40 * 7106704 * 2
def baseEnd_7106704 : Nat := 1216385007076689407205623

theorem tailTrace_7106704 : CollatzResearch.WordTrace tailWord_7106704 prefixEnd_7106704 1216385007076689407205623 := by
  unfold tailWord_7106704
  simp only [CollatzResearch.WordTrace]
  refine ⟨129601394622816305629227583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172801859497088407505636777 129601394622816305629227583)
  ·
    refine ⟨194402091934224458443841375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129601394622816305629227583 194402091934224458443841375)
    ·
      refine ⟨291603137901336687665762063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194402091934224458443841375 291603137901336687665762063)
      ·
        refine ⟨437404706852005031498643095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291603137901336687665762063 437404706852005031498643095)
        ·
          refine ⟨656107060278007547247964643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 437404706852005031498643095 656107060278007547247964643)
          ·
            refine ⟨984160590417011320871946965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 656107060278007547247964643 984160590417011320871946965)
            ·
              refine ⟨23066263837898702832936257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 984160590417011320871946965 23066263837898702832936257)
              ·
                refine ⟨17299697878424027124702193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23066263837898702832936257 17299697878424027124702193)
                ·
                  refine ⟨12974773408818020343526645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17299697878424027124702193 12974773408818020343526645)
                  ·
                    refine ⟨1216385007076689407205623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12974773408818020343526645 1216385007076689407205623)
                    ·
                      rfl

theorem cell23_7106704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 2, 2, 5].length) (baseStart_7106704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7106704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7106704 prefixEnd_7106704 := by exact prefixLift 7106704
  have htrace : WordTrace (prefixWord ++ tailWord_7106704) baseStart_7106704 baseEnd_7106704 := by
    simpa [prefixWord, tailWord_7106704, baseEnd_7106704] using wordTrace_append hprefix tailTrace_7106704
  have hstable : (prefixWord ++ tailWord_7106704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7106704).length < 2 ^ (prefixWord ++ tailWord_7106704).sum := by decide
  have hdescent : baseEnd_7106704 < baseStart_7106704 := by decide
  rcases family_descends (prefixWord ++ tailWord_7106704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7106825 : List Nat := [1, 2, 1, 1, 3, 4, 2, 4, 1, 1, 3]
def baseStart_7106825 : Nat := 118140960795 + 7106825 * 2 ^ 59
def prefixEnd_7106825 : Nat := 4983230072969 + 3 ^ 40 * 7106825 * 2
def baseEnd_7106825 : Nat := 3649217152389262248203813

theorem tailTrace_7106825 : CollatzResearch.WordTrace tailWord_7106825 prefixEnd_7106825 3649217152389262248203813 := by
  unfold tailWord_7106825
  simp only [CollatzResearch.WordTrace]
  refine ⟨259207202478194248923609929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172804801652129499282406619 259207202478194248923609929)
  ·
    refine ⟨194405401858645686692707447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259207202478194248923609929 194405401858645686692707447)
    ·
      refine ⟨291608102787968530039061171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194405401858645686692707447 291608102787968530039061171)
      ·
        refine ⟨437412154181952795058591757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291608102787968530039061171 437412154181952795058591757)
        ·
          refine ⟨164029557818232298146971909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 437412154181952795058591757 164029557818232298146971909)
          ·
            refine ⟨30755542090918555902557233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 164029557818232298146971909 30755542090918555902557233)
            ·
              refine ⟨23066656568188916926917925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30755542090918555902557233 23066656568188916926917925)
              ·
                refine ⟨4324998106535421923797111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23066656568188916926917925 4324998106535421923797111)
                ·
                  refine ⟨6487497159803132885695667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4324998106535421923797111 6487497159803132885695667)
                  ·
                    refine ⟨9731245739704699328543501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6487497159803132885695667 9731245739704699328543501)
                    ·
                      refine ⟨3649217152389262248203813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9731245739704699328543501 3649217152389262248203813)
                      ·
                        rfl

theorem cell23_7106825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 4, 1, 1, 3].length) (baseStart_7106825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7106825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7106825 prefixEnd_7106825 := by exact prefixLift 7106825
  have htrace : WordTrace (prefixWord ++ tailWord_7106825) baseStart_7106825 baseEnd_7106825 := by
    simpa [prefixWord, tailWord_7106825, baseEnd_7106825] using wordTrace_append hprefix tailTrace_7106825
  have hstable : (prefixWord ++ tailWord_7106825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7106825).length < 2 ^ (prefixWord ++ tailWord_7106825).sum := by decide
  have hdescent : baseEnd_7106825 < baseStart_7106825 := by decide
  rcases family_descends (prefixWord ++ tailWord_7106825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7106845 : List Nat := [1, 4, 2, 3, 2, 1, 2, 2, 1, 5]
def baseStart_7106845 : Nat := 118140960795 + 7106845 * 2 ^ 59
def prefixEnd_7106845 : Nat := 4983230072969 + 3 ^ 40 * 7106845 * 2
def baseEnd_7106845 : Nat := 1216409140667450723317907

theorem tailTrace_7106845 : CollatzResearch.WordTrace tailWord_7106845 prefixEnd_7106845 1216409140667450723317907 := by
  unfold tailWord_7106845
  simp only [CollatzResearch.WordTrace]
  refine ⟨259207931938121792339337989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172805287958747861559558659 259207931938121792339337989)
  ·
    refine ⟨48601487238397836063625873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 259207931938121792339337989 48601487238397836063625873)
    ·
      refine ⟨36451115428798377047719405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48601487238397836063625873 36451115428798377047719405)
      ·
        refine ⟨13669168285799391392894777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36451115428798377047719405 13669168285799391392894777)
        ·
          refine ⟨10251876214349543544671083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13669168285799391392894777 10251876214349543544671083)
          ·
            refine ⟨15377814321524315317006625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10251876214349543544671083 15377814321524315317006625)
            ·
              refine ⟨11533360741143236487754969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15377814321524315317006625 11533360741143236487754969)
              ·
                refine ⟨8650020555857427365816227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11533360741143236487754969 8650020555857427365816227)
                ·
                  refine ⟨12975030833786141048724341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8650020555857427365816227 12975030833786141048724341)
                  ·
                    refine ⟨1216409140667450723317907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12975030833786141048724341 1216409140667450723317907)
                    ·
                      rfl

theorem cell23_7106845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 2, 1, 5].length) (baseStart_7106845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7106845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7106845 prefixEnd_7106845 := by exact prefixLift 7106845
  have htrace : WordTrace (prefixWord ++ tailWord_7106845) baseStart_7106845 baseEnd_7106845 := by
    simpa [prefixWord, tailWord_7106845, baseEnd_7106845] using wordTrace_append hprefix tailTrace_7106845
  have hstable : (prefixWord ++ tailWord_7106845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7106845).length < 2 ^ (prefixWord ++ tailWord_7106845).sum := by decide
  have hdescent : baseEnd_7106845 < baseStart_7106845 := by decide
  rcases family_descends (prefixWord ++ tailWord_7106845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7106848 : List Nat := [2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 4]
def baseStart_7106848 : Nat := 118140960795 + 7106848 * 2 ^ 59
def prefixEnd_7106848 : Nat := 4983230072969 + 3 ^ 40 * 7106848 * 2
def baseEnd_7106848 : Nat := 3649228962444315658216207

theorem tailTrace_7106848 : CollatzResearch.WordTrace tailWord_7106848 prefixEnd_7106848 3649228962444315658216207 := by
  unfold tailWord_7106848
  simp only [CollatzResearch.WordTrace]
  refine ⟨129604020678555461925848599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172805360904740615901131465 129604020678555461925848599)
  ·
    refine ⟨194406031017833192888772899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129604020678555461925848599 194406031017833192888772899)
    ·
      refine ⟨291609046526749789333159349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194406031017833192888772899 291609046526749789333159349)
      ·
        refine ⟨27338348111882792749983689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 291609046526749789333159349 27338348111882792749983689)
        ·
          refine ⟨20503761083912094562487767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27338348111882792749983689 20503761083912094562487767)
          ·
            refine ⟨30755641625868141843731651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20503761083912094562487767 30755641625868141843731651)
            ·
              refine ⟨46133462438802212765597477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30755641625868141843731651 46133462438802212765597477)
              ·
                refine ⟨8650024207275414893549527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46133462438802212765597477 8650024207275414893549527)
                ·
                  refine ⟨12975036310913122340324291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8650024207275414893549527 12975036310913122340324291)
                  ·
                    refine ⟨19462554466369683510486437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12975036310913122340324291 19462554466369683510486437)
                    ·
                      refine ⟨3649228962444315658216207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19462554466369683510486437 3649228962444315658216207)
                      ·
                        rfl

theorem cell23_7106848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_7106848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7106848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7106848 prefixEnd_7106848 := by exact prefixLift 7106848
  have htrace : WordTrace (prefixWord ++ tailWord_7106848) baseStart_7106848 baseEnd_7106848 := by
    simpa [prefixWord, tailWord_7106848, baseEnd_7106848] using wordTrace_append hprefix tailTrace_7106848
  have hstable : (prefixWord ++ tailWord_7106848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7106848).length < 2 ^ (prefixWord ++ tailWord_7106848).sum := by decide
  have hdescent : baseEnd_7106848 < baseStart_7106848 := by decide
  rcases family_descends (prefixWord ++ tailWord_7106848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7106868 : List Nat := [2, 5, 1, 1, 1, 2, 1, 3, 1, 1, 5]
def baseStart_7106868 : Nat := 118140960795 + 7106868 * 2 ^ 59
def prefixEnd_7106868 : Nat := 4983230072969 + 3 ^ 40 * 7106868 * 2
def baseEnd_7106868 : Nat := 3649239232057405579966115

theorem tailTrace_7106868 : CollatzResearch.WordTrace tailWord_7106868 prefixEnd_7106868 3649239232057405579966115 := by
  unfold tailWord_7106868
  simp only [CollatzResearch.WordTrace]
  refine ⟨129604385408519233633712629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172805847211358978178283505 129604385408519233633712629)
  ·
    refine ⟨12150411132048678153160559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 129604385408519233633712629 12150411132048678153160559)
    ·
      refine ⟨18225616698073017229740839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12150411132048678153160559 18225616698073017229740839)
      ·
        refine ⟨27338425047109525844611259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18225616698073017229740839 27338425047109525844611259)
        ·
          refine ⟨41007637570664288766916889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27338425047109525844611259 41007637570664288766916889)
          ·
            refine ⟨30755728177998216575187667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41007637570664288766916889 30755728177998216575187667)
            ·
              refine ⟨46133592266997324862781501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30755728177998216575187667 46133592266997324862781501)
              ·
                refine ⟨17300097100123996823543063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46133592266997324862781501 17300097100123996823543063)
                ·
                  refine ⟨25950145650185995235314595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17300097100123996823543063 25950145650185995235314595)
                  ·
                    refine ⟨38925218475278992852971893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25950145650185995235314595 38925218475278992852971893)
                    ·
                      refine ⟨3649239232057405579966115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38925218475278992852971893 3649239232057405579966115)
                      ·
                        rfl

theorem cell23_7106868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_7106868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7106868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7106868 prefixEnd_7106868 := by exact prefixLift 7106868
  have htrace : WordTrace (prefixWord ++ tailWord_7106868) baseStart_7106868 baseEnd_7106868 := by
    simpa [prefixWord, tailWord_7106868, baseEnd_7106868] using wordTrace_append hprefix tailTrace_7106868
  have hstable : (prefixWord ++ tailWord_7106868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7106868).length < 2 ^ (prefixWord ++ tailWord_7106868).sum := by decide
  have hdescent : baseEnd_7106868 < baseStart_7106868 := by decide
  rcases family_descends (prefixWord ++ tailWord_7106868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7106955 : List Nat := [1, 1, 1, 1, 4, 5, 2, 1, 1, 4, 2]
def baseStart_7106955 : Nat := 118140960795 + 7106955 * 2 ^ 59
def prefixEnd_7106955 : Nat := 4983230072969 + 3 ^ 40 * 7106955 * 2
def baseEnd_7106955 : Nat := 3649283904874346739578215

theorem tailTrace_7106955 : CollatzResearch.WordTrace tailWord_7106955 prefixEnd_7106955 3649283904874346739578215 := by
  unfold tailWord_7106955
  simp only [CollatzResearch.WordTrace]
  refine ⟨259211943967723281125842319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172807962645148854083894879 259211943967723281125842319)
  ·
    refine ⟨388817915951584921688763479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259211943967723281125842319 388817915951584921688763479)
    ·
      refine ⟨583226873927377382533145219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388817915951584921688763479 583226873927377382533145219)
      ·
        refine ⟨874840310891066073799717829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 583226873927377382533145219 874840310891066073799717829)
        ·
          refine ⟨164032558292074888837447093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 874840310891066073799717829 164032558292074888837447093)
          ·
            refine ⟨15378052339882020828510665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 164032558292074888837447093 15378052339882020828510665)
            ·
              refine ⟨11533539254911515621382999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15378052339882020828510665 11533539254911515621382999)
              ·
                refine ⟨17300308882367273432074499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11533539254911515621382999 17300308882367273432074499)
                ·
                  refine ⟨25950463323550910148111749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17300308882367273432074499 25950463323550910148111749)
                  ·
                    refine ⟨4865711873165795652770953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25950463323550910148111749 4865711873165795652770953)
                    ·
                      refine ⟨3649283904874346739578215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4865711873165795652770953 3649283904874346739578215)
                      ·
                        rfl

theorem cell23_7106955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 1, 1, 4, 2].length) (baseStart_7106955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7106955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7106955 prefixEnd_7106955 := by exact prefixLift 7106955
  have htrace : WordTrace (prefixWord ++ tailWord_7106955) baseStart_7106955 baseEnd_7106955 := by
    simpa [prefixWord, tailWord_7106955, baseEnd_7106955] using wordTrace_append hprefix tailTrace_7106955
  have hstable : (prefixWord ++ tailWord_7106955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7106955).length < 2 ^ (prefixWord ++ tailWord_7106955).sum := by decide
  have hdescent : baseEnd_7106955 < baseStart_7106955 := by decide
  rcases family_descends (prefixWord ++ tailWord_7106955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7106989 : List Nat := [1, 5, 2, 2, 2, 1, 1, 1, 4, 2, 2]
def baseStart_7106989 : Nat := 118140960795 + 7106989 * 2 ^ 59
def prefixEnd_7106989 : Nat := 4983230072969 + 3 ^ 40 * 7106989 * 2
def baseEnd_7106989 : Nat := 3649301363216599606553059

theorem tailTrace_7106989 : CollatzResearch.WordTrace tailWord_7106989 prefixEnd_7106989 3649301363216599606553059 := by
  unfold tailWord_7106989
  simp only [CollatzResearch.WordTrace]
  refine ⟨259213184049600104932580021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172808789366400069955053347 259213184049600104932580021)
  ·
    refine ⟨24301236004650009837429377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 259213184049600104932580021 24301236004650009837429377)
    ·
      refine ⟨18225927003487507378072033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24301236004650009837429377 18225927003487507378072033)
      ·
        refine ⟨13669445252615630533554025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18225927003487507378072033 13669445252615630533554025)
        ·
          refine ⟨10252083939461722900165519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13669445252615630533554025 10252083939461722900165519)
          ·
            refine ⟨15378125909192584350248279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10252083939461722900165519 15378125909192584350248279)
            ·
              refine ⟨23067188863788876525372419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15378125909192584350248279 23067188863788876525372419)
              ·
                refine ⟨34600783295683314788058629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23067188863788876525372419 34600783295683314788058629)
                ·
                  refine ⟨6487646867940621522760993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34600783295683314788058629 6487646867940621522760993)
                  ·
                    refine ⟨4865735150955466142070745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6487646867940621522760993 4865735150955466142070745)
                    ·
                      refine ⟨3649301363216599606553059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4865735150955466142070745 3649301363216599606553059)
                      ·
                        rfl

theorem cell23_7106989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_7106989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7106989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7106989 prefixEnd_7106989 := by exact prefixLift 7106989
  have htrace : WordTrace (prefixWord ++ tailWord_7106989) baseStart_7106989 baseEnd_7106989 := by
    simpa [prefixWord, tailWord_7106989, baseEnd_7106989] using wordTrace_append hprefix tailTrace_7106989
  have hstable : (prefixWord ++ tailWord_7106989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7106989).length < 2 ^ (prefixWord ++ tailWord_7106989).sum := by decide
  have hdescent : baseEnd_7106989 < baseStart_7106989 := by decide
  rcases family_descends (prefixWord ++ tailWord_7106989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7107031 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 4, 3, 5]
def baseStart_7107031 : Nat := 118140960795 + 7107031 * 2 ^ 59
def prefixEnd_7107031 : Nat := 4983230072969 + 3 ^ 40 * 7107031 * 2
def baseEnd_7107031 : Nat := 3649322929404088442227865

theorem tailTrace_7107031 : CollatzResearch.WordTrace tailWord_7107031 prefixEnd_7107031 3649322929404088442227865 := by
  unfold tailWord_7107031
  simp only [CollatzResearch.WordTrace]
  refine ⟨259214715915447946105608947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172809810610298630737072631 259214715915447946105608947)
  ·
    refine ⟨388822073873171919158413421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259214715915447946105608947 388822073873171919158413421)
    ·
      refine ⟨145808277702439469684405033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 388822073873171919158413421 145808277702439469684405033)
      ·
        refine ⟨109356208276829602263303775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145808277702439469684405033 109356208276829602263303775)
        ·
          refine ⟨164034312415244403394955663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109356208276829602263303775 164034312415244403394955663)
          ·
            refine ⟨246051468622866605092433495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164034312415244403394955663 246051468622866605092433495)
            ·
              refine ⟨369077202934299907638650243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246051468622866605092433495 369077202934299907638650243)
              ·
                refine ⟨553615804401449861457975365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 369077202934299907638650243 553615804401449861457975365)
                ·
                  refine ⟨103802963325271849023370381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 553615804401449861457975365 103802963325271849023370381)
                  ·
                    refine ⟨38926111246976943383763893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 103802963325271849023370381 38926111246976943383763893)
                    ·
                      refine ⟨3649322929404088442227865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38926111246976943383763893 3649322929404088442227865)
                      ·
                        rfl

theorem cell23_7107031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_7107031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7107031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7107031 prefixEnd_7107031 := by exact prefixLift 7107031
  have htrace : WordTrace (prefixWord ++ tailWord_7107031) baseStart_7107031 baseEnd_7107031 := by
    simpa [prefixWord, tailWord_7107031, baseEnd_7107031] using wordTrace_append hprefix tailTrace_7107031
  have hstable : (prefixWord ++ tailWord_7107031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7107031).length < 2 ^ (prefixWord ++ tailWord_7107031).sum := by decide
  have hdescent : baseEnd_7107031 < baseStart_7107031 := by decide
  rcases family_descends (prefixWord ++ tailWord_7107031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7107051 : List Nat := [1, 1, 1, 1, 2, 3, 3, 3, 8]
def baseStart_7107051 : Nat := 118140960795 + 7107051 * 2 ^ 59
def prefixEnd_7107051 : Nat := 4983230072969 + 3 ^ 40 * 7107051 * 2
def baseEnd_7107051 : Nat := 405481466557464262664197

theorem tailTrace_7107051 : CollatzResearch.WordTrace tailWord_7107051 prefixEnd_7107051 405481466557464262664197 := by
  unfold tailWord_7107051
  simp only [CollatzResearch.WordTrace]
  refine ⟨259215445375375489521337007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172810296916916993014224671 259215445375375489521337007)
  ·
    refine ⟨388823168063063234282005511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259215445375375489521337007 388823168063063234282005511)
    ·
      refine ⟨583234752094594851423008267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388823168063063234282005511 583234752094594851423008267)
      ·
        refine ⟨874852128141892277134512401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 583234752094594851423008267 874852128141892277134512401)
        ·
          refine ⟨656139096106419207850884301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 874852128141892277134512401 656139096106419207850884301)
          ·
            refine ⟨246052161039907202944081613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 656139096106419207850884301 246052161039907202944081613)
            ·
              refine ⟨92269560389965201104030605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 246052161039907202944081613 92269560389965201104030605)
              ·
                refine ⟨34601085146236950414011477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92269560389965201104030605 34601085146236950414011477)
                ·
                  refine ⟨405481466557464262664197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34601085146236950414011477 405481466557464262664197)
                  ·
                    rfl

theorem cell23_7107051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 8].length) (baseStart_7107051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7107051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7107051 prefixEnd_7107051 := by exact prefixLift 7107051
  have htrace : WordTrace (prefixWord ++ tailWord_7107051) baseStart_7107051 baseEnd_7107051 := by
    simpa [prefixWord, tailWord_7107051, baseEnd_7107051] using wordTrace_append hprefix tailTrace_7107051
  have hstable : (prefixWord ++ tailWord_7107051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7107051).length < 2 ^ (prefixWord ++ tailWord_7107051).sum := by decide
  have hdescent : baseEnd_7107051 < baseStart_7107051 := by decide
  rcases family_descends (prefixWord ++ tailWord_7107051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7107135 : List Nat := [1, 1, 2, 2, 3, 2, 2, 4, 1, 1, 4]
def baseStart_7107135 : Nat := 118140960795 + 7107135 * 2 ^ 59
def prefixEnd_7107135 : Nat := 4983230072969 + 3 ^ 40 * 7107135 * 2
def baseEnd_7107135 : Nat := 3649376331392156035327387

theorem tailTrace_7107135 : CollatzResearch.WordTrace tailWord_7107135 prefixEnd_7107135 3649376331392156035327387 := by
  unfold tailWord_7107135
  simp only [CollatzResearch.WordTrace]
  refine ⟨259218509107071171867394859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172812339404714114578263239 259218509107071171867394859)
  ·
    refine ⟨388827763660606757801092289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259218509107071171867394859 388827763660606757801092289)
    ·
      refine ⟨291620822745455068350819217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 388827763660606757801092289 291620822745455068350819217)
      ·
        refine ⟨218715617059091301263114413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291620822745455068350819217 218715617059091301263114413)
        ·
          refine ⟨82018356397159237973667905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218715617059091301263114413 82018356397159237973667905)
          ·
            refine ⟨61513767297869428480250929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82018356397159237973667905 61513767297869428480250929)
            ·
              refine ⟨46135325473402071360188197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61513767297869428480250929 46135325473402071360188197)
              ·
                refine ⟨8650373526262888380035287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46135325473402071360188197 8650373526262888380035287)
                ·
                  refine ⟨12975560289394332570052931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8650373526262888380035287 12975560289394332570052931)
                  ·
                    refine ⟨19463340434091498855079397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12975560289394332570052931 19463340434091498855079397)
                    ·
                      refine ⟨3649376331392156035327387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19463340434091498855079397 3649376331392156035327387)
                      ·
                        rfl

theorem cell23_7107135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 4, 1, 1, 4].length) (baseStart_7107135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7107135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7107135 prefixEnd_7107135 := by exact prefixLift 7107135
  have htrace : WordTrace (prefixWord ++ tailWord_7107135) baseStart_7107135 baseEnd_7107135 := by
    simpa [prefixWord, tailWord_7107135, baseEnd_7107135] using wordTrace_append hprefix tailTrace_7107135
  have hstable : (prefixWord ++ tailWord_7107135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7107135).length < 2 ^ (prefixWord ++ tailWord_7107135).sum := by decide
  have hdescent : baseEnd_7107135 < baseStart_7107135 := by decide
  rcases family_descends (prefixWord ++ tailWord_7107135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7107149 : List Nat := [1, 6, 1, 1, 2, 1, 4, 1, 1, 5]
def baseStart_7107149 : Nat := 118140960795 + 7107149 * 2 ^ 59
def prefixEnd_7107149 : Nat := 4983230072969 + 3 ^ 40 * 7107149 * 2
def baseEnd_7107149 : Nat := 1216461173373772993517441

theorem tailTrace_7107149 : CollatzResearch.WordTrace tailWord_7107149 prefixEnd_7107149 1216461173373772993517441 := by
  unfold tailWord_7107149
  simp only [CollatzResearch.WordTrace]
  refine ⟨259219019729020452258404501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172812679819346968172269667 259219019729020452258404501)
  ·
    refine ⟨12150891549797833699612711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 259219019729020452258404501 12150891549797833699612711)
    ·
      refine ⟨18226337324696750549419067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12150891549797833699612711 18226337324696750549419067)
      ·
        refine ⟨27339505987045125824128601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18226337324696750549419067 27339505987045125824128601)
        ·
          refine ⟨20504629490283844368096451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27339505987045125824128601 20504629490283844368096451)
          ·
            refine ⟨30756944235425766552144677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20504629490283844368096451 30756944235425766552144677)
            ·
              refine ⟨5766927044142331228527127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30756944235425766552144677 5766927044142331228527127)
              ·
                refine ⟨8650390566213496842790691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5766927044142331228527127 8650390566213496842790691)
                ·
                  refine ⟨12975585849320245264186037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8650390566213496842790691 12975585849320245264186037)
                  ·
                    refine ⟨1216461173373772993517441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12975585849320245264186037 1216461173373772993517441)
                    ·
                      rfl

theorem cell23_7107149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_7107149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7107149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7107149 prefixEnd_7107149 := by exact prefixLift 7107149
  have htrace : WordTrace (prefixWord ++ tailWord_7107149) baseStart_7107149 baseEnd_7107149 := by
    simpa [prefixWord, tailWord_7107149, baseEnd_7107149] using wordTrace_append hprefix tailTrace_7107149
  have hstable : (prefixWord ++ tailWord_7107149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7107149).length < 2 ^ (prefixWord ++ tailWord_7107149).sum := by decide
  have hdescent : baseEnd_7107149 < baseStart_7107149 := by decide
  rcases family_descends (prefixWord ++ tailWord_7107149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7107169 : List Nat := [1, 2, 3, 1, 1, 5, 2, 1, 3, 2, 2]
def baseStart_7107169 : Nat := 118140960795 + 7107169 * 2 ^ 59
def prefixEnd_7107169 : Nat := 4983230072969 + 3 ^ 40 * 7107169 * 2
def baseEnd_7107169 : Nat := 3649393789734408902302231

theorem tailTrace_7107169 : CollatzResearch.WordTrace tailWord_7107169 prefixEnd_7107169 3649393789734408902302231 := by
  unfold tailWord_7107169
  simp only [CollatzResearch.WordTrace]
  refine ⟨259219749188947995674132561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172813166125965330449421707 259219749188947995674132561)
  ·
    refine ⟨194414811891710996755599421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259219749188947995674132561 194414811891710996755599421)
    ·
      refine ⟨72905554459391623783349783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194414811891710996755599421 72905554459391623783349783)
      ·
        refine ⟨109358331689087435675024675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72905554459391623783349783 109358331689087435675024675)
        ·
          refine ⟨164037497533631153512537013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109358331689087435675024675 164037497533631153512537013)
          ·
            refine ⟨15378515393777920641800345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 164037497533631153512537013 15378515393777920641800345)
            ·
              refine ⟨11533886545333440481350259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15378515393777920641800345 11533886545333440481350259)
              ·
                refine ⟨17300829818000160722025389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11533886545333440481350259 17300829818000160722025389)
                ·
                  refine ⟨6487811181750060270759521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17300829818000160722025389 6487811181750060270759521)
                  ·
                    refine ⟨4865858386312545203069641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6487811181750060270759521 4865858386312545203069641)
                    ·
                      refine ⟨3649393789734408902302231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4865858386312545203069641 3649393789734408902302231)
                      ·
                        rfl

theorem cell23_7107169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 1, 3, 2, 2].length) (baseStart_7107169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7107169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7107169 prefixEnd_7107169 := by exact prefixLift 7107169
  have htrace : WordTrace (prefixWord ++ tailWord_7107169) baseStart_7107169 baseEnd_7107169 := by
    simpa [prefixWord, tailWord_7107169, baseEnd_7107169] using wordTrace_append hprefix tailTrace_7107169
  have hstable : (prefixWord ++ tailWord_7107169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7107169).length < 2 ^ (prefixWord ++ tailWord_7107169).sum := by decide
  have hdescent : baseEnd_7107169 < baseStart_7107169 := by decide
  rcases family_descends (prefixWord ++ tailWord_7107169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7107182 : List Nat := [4, 1, 2, 2, 2, 1, 3, 1, 1, 2, 4]
def baseStart_7107182 : Nat := 118140960795 + 7107182 * 2 ^ 59
def prefixEnd_7107182 : Nat := 4983230072969 + 3 ^ 40 * 7107182 * 2
def baseEnd_7107182 : Nat := 3649400464982917351439671

theorem tailTrace_7107182 : CollatzResearch.WordTrace tailWord_7107182 prefixEnd_7107182 3649400464982917351439671 := by
  unfold tailWord_7107182
  simp only [CollatzResearch.WordTrace]
  refine ⟨32402527917237612361794475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172813482225267265929570533 32402527917237612361794475)
  ·
    refine ⟨48603791875856418542691713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32402527917237612361794475 48603791875856418542691713)
    ·
      refine ⟨36452843906892313907018785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48603791875856418542691713 36452843906892313907018785)
      ·
        refine ⟨27339632930169235430264089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36452843906892313907018785 27339632930169235430264089)
        ·
          refine ⟨20504724697626926572698067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27339632930169235430264089 20504724697626926572698067)
          ·
            refine ⟨30757087046440389859047101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20504724697626926572698067 30757087046440389859047101)
            ·
              refine ⟨11533907642415146197142663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30757087046440389859047101 11533907642415146197142663)
              ·
                refine ⟨17300861463622719295713995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11533907642415146197142663 17300861463622719295713995)
                ·
                  refine ⟨25951292195434078943570993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17300861463622719295713995 25951292195434078943570993)
                  ·
                    refine ⟨19463469146575559207678245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25951292195434078943570993 19463469146575559207678245)
                    ·
                      refine ⟨3649400464982917351439671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19463469146575559207678245 3649400464982917351439671)
                      ·
                        rfl

theorem cell23_7107182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_7107182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7107182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7107182 prefixEnd_7107182 := by exact prefixLift 7107182
  have htrace : WordTrace (prefixWord ++ tailWord_7107182) baseStart_7107182 baseEnd_7107182 := by
    simpa [prefixWord, tailWord_7107182, baseEnd_7107182] using wordTrace_append hprefix tailTrace_7107182
  have hstable : (prefixWord ++ tailWord_7107182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7107182).length < 2 ^ (prefixWord ++ tailWord_7107182).sum := by decide
  have hdescent : baseEnd_7107182 < baseStart_7107182 := by decide
  rcases family_descends (prefixWord ++ tailWord_7107182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7107220 : List Nat := [2, 4, 2, 2, 1, 2, 3, 2, 1, 2, 2]
def baseStart_7107220 : Nat := 118140960795 + 7107220 * 2 ^ 59
def prefixEnd_7107220 : Nat := 4983230072969 + 3 ^ 40 * 7107220 * 2
def baseEnd_7107220 : Nat := 3649419977247788202764497

theorem tailTrace_7107220 : CollatzResearch.WordTrace tailWord_7107220 prefixEnd_7107220 3649419977247788202764497 := by
  unfold tailWord_7107220
  simp only [CollatzResearch.WordTrace]
  refine ⟨129610804655881615692119557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172814406207842154256159409 129610804655881615692119557)
  ·
    refine ⟨24302025872977802942272417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129610804655881615692119557 24302025872977802942272417)
    ·
      refine ⟨18226519404733352206704313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24302025872977802942272417 18226519404733352206704313)
      ·
        refine ⟨13669889553550014155028235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18226519404733352206704313 13669889553550014155028235)
        ·
          refine ⟨20504834330325021232542353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13669889553550014155028235 20504834330325021232542353)
          ·
            refine ⟨15378625747743765924406765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20504834330325021232542353 15378625747743765924406765)
            ·
              refine ⟨5766984655403912221652537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15378625747743765924406765 5766984655403912221652537)
              ·
                refine ⟨4325238491552934166239403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5766984655403912221652537 4325238491552934166239403)
                ·
                  refine ⟨6487857737329401249359105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4325238491552934166239403 6487857737329401249359105)
                  ·
                    refine ⟨4865893302997050937019329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6487857737329401249359105 4865893302997050937019329)
                    ·
                      refine ⟨3649419977247788202764497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4865893302997050937019329 3649419977247788202764497)
                      ·
                        rfl

theorem cell23_7107220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_7107220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7107220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7107220 prefixEnd_7107220 := by exact prefixLift 7107220
  have htrace : WordTrace (prefixWord ++ tailWord_7107220) baseStart_7107220 baseEnd_7107220 := by
    simpa [prefixWord, tailWord_7107220, baseEnd_7107220] using wordTrace_append hprefix tailTrace_7107220
  have hstable : (prefixWord ++ tailWord_7107220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7107220).length < 2 ^ (prefixWord ++ tailWord_7107220).sum := by decide
  have hdescent : baseEnd_7107220 < baseStart_7107220 := by decide
  rcases family_descends (prefixWord ++ tailWord_7107220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7107246 : List Nat := [4, 1, 4, 1, 1, 2, 1, 1, 3, 3, 2]
def baseStart_7107246 : Nat := 118140960795 + 7107246 * 2 ^ 59
def prefixEnd_7107246 : Nat := 4983230072969 + 3 ^ 40 * 7107246 * 2
def baseEnd_7107246 : Nat := 3649433327744805101039377

theorem tailTrace_7107246 : CollatzResearch.WordTrace tailWord_7107246 prefixEnd_7107246 3649433327744805101039377 := by
  unfold tailWord_7107246
  simp only [CollatzResearch.WordTrace]
  refine ⟨32402819701208629728085699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172815038406446025216457061 32402819701208629728085699)
  ·
    refine ⟨48604229551812944592128549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32402819701208629728085699 48604229551812944592128549)
    ·
      refine ⟨9113293040964927111024103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48604229551812944592128549 9113293040964927111024103)
      ·
        refine ⟨13669939561447390666536155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9113293040964927111024103 13669939561447390666536155)
        ·
          refine ⟨20504909342171085999804233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13669939561447390666536155 20504909342171085999804233)
          ·
            refine ⟨15378682006628314499853175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20504909342171085999804233 15378682006628314499853175)
            ·
              refine ⟨23068023009942471749779763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15378682006628314499853175 23068023009942471749779763)
              ·
                refine ⟨34602034514913707624669645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23068023009942471749779763 34602034514913707624669645)
                ·
                  refine ⟨12975762943092640359251117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34602034514913707624669645 12975762943092640359251117)
                  ·
                    refine ⟨4865911103659740134719169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12975762943092640359251117 4865911103659740134719169)
                    ·
                      refine ⟨3649433327744805101039377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4865911103659740134719169 3649433327744805101039377)
                      ·
                        rfl

theorem cell23_7107246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_7107246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7107246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7107246 prefixEnd_7107246 := by exact prefixLift 7107246
  have htrace : WordTrace (prefixWord ++ tailWord_7107246) baseStart_7107246 baseEnd_7107246 := by
    simpa [prefixWord, tailWord_7107246, baseEnd_7107246] using wordTrace_append hprefix tailTrace_7107246
  have hstable : (prefixWord ++ tailWord_7107246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7107246).length < 2 ^ (prefixWord ++ tailWord_7107246).sum := by decide
  have hdescent : baseEnd_7107246 < baseStart_7107246 := by decide
  rcases family_descends (prefixWord ++ tailWord_7107246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7107248 : List Nat := [2, 1, 1, 1, 2, 1, 3, 3, 9]
def baseStart_7107248 : Nat := 118140960795 + 7107248 * 2 ^ 59
def prefixEnd_7107248 : Nat := 4983230072969 + 3 ^ 40 * 7107248 * 2
def baseEnd_7107248 : Nat := 405492706078457121468263

theorem tailTrace_7107248 : CollatzResearch.WordTrace tailWord_7107248 prefixEnd_7107248 405492706078457121468263 := by
  unfold tailWord_7107248
  simp only [CollatzResearch.WordTrace]
  refine ⟨129611315277830896083129199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172815087037107861444172265 129611315277830896083129199)
  ·
    refine ⟨194416972916746344124693799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129611315277830896083129199 194416972916746344124693799)
    ·
      refine ⟨291625459375119516187040699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194416972916746344124693799 291625459375119516187040699)
      ·
        refine ⟨437438189062679274280561049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291625459375119516187040699 437438189062679274280561049)
        ·
          refine ⟨328078641797009455710420787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 437438189062679274280561049 328078641797009455710420787)
          ·
            refine ⟨492117962695514183565631181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328078641797009455710420787 492117962695514183565631181)
            ·
              refine ⟨184544236010817818837111693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 492117962695514183565631181 184544236010817818837111693)
              ·
                refine ⟨69204088504056682063916885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 184544236010817818837111693 69204088504056682063916885)
                ·
                  refine ⟨405492706078457121468263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 69204088504056682063916885 405492706078457121468263)
                  ·
                    rfl

theorem cell23_7107248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 9].length) (baseStart_7107248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7107248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7107248 prefixEnd_7107248 := by exact prefixLift 7107248
  have htrace : WordTrace (prefixWord ++ tailWord_7107248) baseStart_7107248 baseEnd_7107248 := by
    simpa [prefixWord, tailWord_7107248, baseEnd_7107248] using wordTrace_append hprefix tailTrace_7107248
  have hstable : (prefixWord ++ tailWord_7107248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7107248).length < 2 ^ (prefixWord ++ tailWord_7107248).sum := by decide
  have hdescent : baseEnd_7107248 < baseStart_7107248 := by decide
  rcases family_descends (prefixWord ++ tailWord_7107248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7107270 : List Nat := [6, 1, 2, 1, 2, 1, 2, 2, 2, 1, 3]
def baseStart_7107270 : Nat := 118140960795 + 7107270 * 2 ^ 59
def prefixEnd_7107270 : Nat := 4983230072969 + 3 ^ 40 * 7107270 * 2
def baseEnd_7107270 : Nat := 3649445651280513007139267

theorem tailTrace_7107270 : CollatzResearch.WordTrace tailWord_7107270 prefixEnd_7107270 3649445651280513007139267 := by
  unfold tailWord_7107270
  simp only [CollatzResearch.WordTrace]
  refine ⟨8100732280049440310111227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 172815621974388059949039509 8100732280049440310111227)
  ·
    refine ⟨12151098420074160465166841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8100732280049440310111227 12151098420074160465166841)
    ·
      refine ⟨9113323815055620348875131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12151098420074160465166841 9113323815055620348875131)
      ·
        refine ⟨13669985722583430523312697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9113323815055620348875131 13669985722583430523312697)
        ·
          refine ⟨10252489291937572892484523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13669985722583430523312697 10252489291937572892484523)
          ·
            refine ⟨15378733937906359338726785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10252489291937572892484523 15378733937906359338726785)
            ·
              refine ⟨11534050453429769504045089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15378733937906359338726785 11534050453429769504045089)
              ·
                refine ⟨8650537840072327128033817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11534050453429769504045089 8650537840072327128033817)
                ·
                  refine ⟨6487903380054245346025363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8650537840072327128033817 6487903380054245346025363)
                  ·
                    refine ⟨9731855070081368019038045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6487903380054245346025363 9731855070081368019038045)
                    ·
                      refine ⟨3649445651280513007139267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9731855070081368019038045 3649445651280513007139267)
                      ·
                        rfl

theorem cell23_7107270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_7107270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7107270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7107270 prefixEnd_7107270 := by exact prefixLift 7107270
  have htrace : WordTrace (prefixWord ++ tailWord_7107270) baseStart_7107270 baseEnd_7107270 := by
    simpa [prefixWord, tailWord_7107270, baseEnd_7107270] using wordTrace_append hprefix tailTrace_7107270
  have hstable : (prefixWord ++ tailWord_7107270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7107270).length < 2 ^ (prefixWord ++ tailWord_7107270).sum := by decide
  have hdescent : baseEnd_7107270 < baseStart_7107270 := by decide
  rcases family_descends (prefixWord ++ tailWord_7107270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7107276 : List Nat := [2, 2, 1, 5, 1, 1, 1, 4, 2, 2, 2]
def baseStart_7107276 : Nat := 118140960795 + 7107276 * 2 ^ 59
def prefixEnd_7107276 : Nat := 4983230072969 + 3 ^ 40 * 7107276 * 2
def baseEnd_7107276 : Nat := 3649448732164439983664239

theorem tailTrace_7107276 : CollatzResearch.WordTrace tailWord_7107276 prefixEnd_7107276 3649448732164439983664239 := by
  unfold tailWord_7107276
  simp only [CollatzResearch.WordTrace]
  refine ⟨129611825899780176474138841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172815767866373568632185121 129611825899780176474138841)
  ·
    refine ⟨97208869424835132355604131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129611825899780176474138841 97208869424835132355604131)
    ·
      refine ⟨145813304137252698533406197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97208869424835132355604131 145813304137252698533406197)
      ·
        refine ⟨13669997262867440487506831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 145813304137252698533406197 13669997262867440487506831)
        ·
          refine ⟨20504995894301160731260247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13669997262867440487506831 20504995894301160731260247)
          ·
            refine ⟨30757493841451741096890371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20504995894301160731260247 30757493841451741096890371)
            ·
              refine ⟨46136240762177611645335557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30757493841451741096890371 46136240762177611645335557)
              ·
                refine ⟨8650545142908302183500417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46136240762177611645335557 8650545142908302183500417)
                ·
                  refine ⟨6487908857181226637625313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8650545142908302183500417 6487908857181226637625313)
                  ·
                    refine ⟨4865931642885919978218985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6487908857181226637625313 4865931642885919978218985)
                    ·
                      refine ⟨3649448732164439983664239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4865931642885919978218985 3649448732164439983664239)
                      ·
                        rfl

theorem cell23_7107276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_7107276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7107276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7107276 prefixEnd_7107276 := by exact prefixLift 7107276
  have htrace : WordTrace (prefixWord ++ tailWord_7107276) baseStart_7107276 baseEnd_7107276 := by
    simpa [prefixWord, tailWord_7107276, baseEnd_7107276] using wordTrace_append hprefix tailTrace_7107276
  have hstable : (prefixWord ++ tailWord_7107276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7107276).length < 2 ^ (prefixWord ++ tailWord_7107276).sum := by decide
  have hdescent : baseEnd_7107276 < baseStart_7107276 := by decide
  rcases family_descends (prefixWord ++ tailWord_7107276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7107332 : List Nat := [2, 3, 2, 2, 1, 1, 2, 1, 4, 1, 4]
def baseStart_7107332 : Nat := 118140960795 + 7107332 * 2 ^ 59
def prefixEnd_7107332 : Nat := 4983230072969 + 3 ^ 40 * 7107332 * 2
def baseEnd_7107332 : Nat := 3649477487081091764563981

theorem tailTrace_7107332 : CollatzResearch.WordTrace tailWord_7107332 prefixEnd_7107332 3649477487081091764563981 := by
  unfold tailWord_7107332
  simp only [CollatzResearch.WordTrace]
  refine ⟨129612847143678737256158125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172817129524904983008210833 129612847143678737256158125)
  ·
    refine ⟨48604817678879526471059297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129612847143678737256158125 48604817678879526471059297)
    ·
      refine ⟨36453613259159644853294473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48604817678879526471059297 36453613259159644853294473)
      ·
        refine ⟨27340209944369733639970855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36453613259159644853294473 27340209944369733639970855)
        ·
          refine ⟨41010314916554600459956283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27340209944369733639970855 41010314916554600459956283)
          ·
            refine ⟨61515472374831900689934425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41010314916554600459956283 61515472374831900689934425)
            ·
              refine ⟨46136604281123925517450819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61515472374831900689934425 46136604281123925517450819)
              ·
                refine ⟨69204906421685888276176229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46136604281123925517450819 69204906421685888276176229)
                ·
                  refine ⟨12975919954066104051783043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69204906421685888276176229 12975919954066104051783043)
                  ·
                    refine ⟨19463879931099156077674565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12975919954066104051783043 19463879931099156077674565)
                    ·
                      refine ⟨3649477487081091764563981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19463879931099156077674565 3649477487081091764563981)
                      ·
                        rfl

theorem cell23_7107332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_7107332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7107332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7107332 prefixEnd_7107332 := by exact prefixLift 7107332
  have htrace : WordTrace (prefixWord ++ tailWord_7107332) baseStart_7107332 baseEnd_7107332 := by
    simpa [prefixWord, tailWord_7107332, baseEnd_7107332] using wordTrace_append hprefix tailTrace_7107332
  have hstable : (prefixWord ++ tailWord_7107332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7107332).length < 2 ^ (prefixWord ++ tailWord_7107332).sum := by decide
  have hdescent : baseEnd_7107332 < baseStart_7107332 := by decide
  rcases family_descends (prefixWord ++ tailWord_7107332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7107393 : List Nat := [1, 2, 5, 3, 1, 2, 1, 1, 3, 4]
def baseStart_7107393 : Nat := 118140960795 + 7107393 * 2 ^ 59
def prefixEnd_7107393 : Nat := 4983230072969 + 3 ^ 40 * 7107393 * 2
def baseEnd_7107393 : Nat := 1216502936467005341967067

theorem tailTrace_7107393 : CollatzResearch.WordTrace tailWord_7107393 prefixEnd_7107393 1216502936467005341967067 := by
  unfold tailWord_7107393
  simp only [CollatzResearch.WordTrace]
  refine ⟨259227919140136481930286833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172818612760090987953524555 259227919140136481930286833)
  ·
    refine ⟨194420939355102361447715125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259227919140136481930286833 194420939355102361447715125)
    ·
      refine ⟨18226963064540846385723293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 194420939355102361447715125 18226963064540846385723293)
      ·
        refine ⟨6835111149202817394646235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18226963064540846385723293 6835111149202817394646235)
        ·
          refine ⟨10252666723804226091969353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6835111149202817394646235 10252666723804226091969353)
          ·
            refine ⟨7689500042853169568977015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10252666723804226091969353 7689500042853169568977015)
            ·
              refine ⟨11534250064279754353465523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7689500042853169568977015 11534250064279754353465523)
              ·
                refine ⟨17301375096419631530198285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11534250064279754353465523 17301375096419631530198285)
                ·
                  refine ⟨6488015661157361823824357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17301375096419631530198285 6488015661157361823824357)
                  ·
                    refine ⟨1216502936467005341967067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6488015661157361823824357 1216502936467005341967067)
                    ·
                      rfl

theorem cell23_7107393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_7107393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7107393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7107393 prefixEnd_7107393 := by exact prefixLift 7107393
  have htrace : WordTrace (prefixWord ++ tailWord_7107393) baseStart_7107393 baseEnd_7107393 := by
    simpa [prefixWord, tailWord_7107393, baseEnd_7107393] using wordTrace_append hprefix tailTrace_7107393
  have hstable : (prefixWord ++ tailWord_7107393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7107393).length < 2 ^ (prefixWord ++ tailWord_7107393).sum := by decide
  have hdescent : baseEnd_7107393 < baseStart_7107393 := by decide
  rcases family_descends (prefixWord ++ tailWord_7107393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7107432 : List Nat := [2, 1, 4, 2, 1, 2, 1, 1, 3, 6]
def baseStart_7107432 : Nat := 118140960795 + 7107432 * 2 ^ 59
def prefixEnd_7107432 : Nat := 4983230072969 + 3 ^ 40 * 7107432 * 2
def baseEnd_7107432 : Nat := 1216509611715513791104507

theorem tailTrace_7107432 : CollatzResearch.WordTrace tailWord_7107432 prefixEnd_7107432 1216509611715513791104507 := by
  unfold tailWord_7107432
  simp only [CollatzResearch.WordTrace]
  refine ⟨129614670793497595795478275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172819561057996794393971033 129614670793497595795478275)
  ·
    refine ⟨194422006190246393693217413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129614670793497595795478275 194422006190246393693217413)
    ·
      refine ⟨36454126160671198817478265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 194422006190246393693217413 36454126160671198817478265)
      ·
        refine ⟨27340594620503399113108699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36454126160671198817478265 27340594620503399113108699)
        ·
          refine ⟨41010891930755098669663049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27340594620503399113108699 41010891930755098669663049)
          ·
            refine ⟨30758168948066324002247287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41010891930755098669663049 30758168948066324002247287)
            ·
              refine ⟨46137253422099486003370931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30758168948066324002247287 46137253422099486003370931)
              ·
                refine ⟨69205880133149229005056397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46137253422099486003370931 69205880133149229005056397)
                ·
                  refine ⟨25952205049930960876896149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69205880133149229005056397 25952205049930960876896149)
                  ·
                    refine ⟨1216509611715513791104507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25952205049930960876896149 1216509611715513791104507)
                    ·
                      rfl

theorem cell23_7107432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_7107432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7107432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7107432 prefixEnd_7107432 := by exact prefixLift 7107432
  have htrace : WordTrace (prefixWord ++ tailWord_7107432) baseStart_7107432 baseEnd_7107432 := by
    simpa [prefixWord, tailWord_7107432, baseEnd_7107432] using wordTrace_append hprefix tailTrace_7107432
  have hstable : (prefixWord ++ tailWord_7107432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7107432).length < 2 ^ (prefixWord ++ tailWord_7107432).sum := by decide
  have hdescent : baseEnd_7107432 < baseStart_7107432 := by decide
  rcases family_descends (prefixWord ++ tailWord_7107432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7107449 : List Nat := [1, 2, 1, 3, 2, 3, 1, 4, 2, 4]
def baseStart_7107449 : Nat := 118140960795 + 7107449 * 2 ^ 59
def prefixEnd_7107449 : Nat := 4983230072969 + 3 ^ 40 * 7107449 * 2
def baseEnd_7107449 : Nat := 1216512521439222602266981

theorem tailTrace_7107449 : CollatzResearch.WordTrace tailWord_7107449 prefixEnd_7107449 1216512521439222602266981 := by
  unfold tailWord_7107449
  simp only [CollatzResearch.WordTrace]
  refine ⟨259229961627933603494325401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172819974418622402329550267 259229961627933603494325401)
  ·
    refine ⟨194422471220950202620744051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259229961627933603494325401 194422471220950202620744051)
    ·
      refine ⟨291633706831425303931116077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194422471220950202620744051 291633706831425303931116077)
      ·
        refine ⟨109362640061784488974168529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 291633706831425303931116077 109362640061784488974168529)
        ·
          refine ⟨82021980046338366730626397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109362640061784488974168529 82021980046338366730626397)
          ·
            refine ⟨30758242517376887523984899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82021980046338366730626397 30758242517376887523984899)
            ·
              refine ⟨46137363776065331285977349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30758242517376887523984899 46137363776065331285977349)
              ·
                refine ⟨8650755708012249616120753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46137363776065331285977349 8650755708012249616120753)
                ·
                  refine ⟨6488066781009187212090565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8650755708012249616120753 6488066781009187212090565)
                  ·
                    refine ⟨1216512521439222602266981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6488066781009187212090565 1216512521439222602266981)
                    ·
                      rfl

theorem cell23_7107449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 4, 2, 4].length) (baseStart_7107449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7107449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7107449 prefixEnd_7107449 := by exact prefixLift 7107449
  have htrace : WordTrace (prefixWord ++ tailWord_7107449) baseStart_7107449 baseEnd_7107449 := by
    simpa [prefixWord, tailWord_7107449, baseEnd_7107449] using wordTrace_append hprefix tailTrace_7107449
  have hstable : (prefixWord ++ tailWord_7107449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7107449).length < 2 ^ (prefixWord ++ tailWord_7107449).sum := by decide
  have hdescent : baseEnd_7107449 < baseStart_7107449 := by decide
  rcases family_descends (prefixWord ++ tailWord_7107449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7107466 : List Nat := [3, 1, 2, 4, 1, 1, 2, 3, 2, 4]
def baseStart_7107466 : Nat := 118140960795 + 7107466 * 2 ^ 59
def prefixEnd_7107466 : Nat := 4983230072969 + 3 ^ 40 * 7107466 * 2
def baseEnd_7107466 : Nat := 1216515431162931413429455

theorem tailTrace_7107466 : CollatzResearch.WordTrace tailWord_7107466 prefixEnd_7107466 1216515431162931413429455 := by
  unfold tailWord_7107466
  simp only [CollatzResearch.WordTrace]
  refine ⟨64807645417218003849423563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172820387779248010265129501 64807645417218003849423563)
  ·
    refine ⟨97211468125827005774135345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64807645417218003849423563 97211468125827005774135345)
    ·
      refine ⟨72908601094370254330601509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97211468125827005774135345 72908601094370254330601509)
      ·
        refine ⟨13670362705194422686987783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72908601094370254330601509 13670362705194422686987783)
        ·
          refine ⟨20505544057791634030481675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13670362705194422686987783 20505544057791634030481675)
          ·
            refine ⟨30758316086687451045722513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20505544057791634030481675 30758316086687451045722513)
            ·
              refine ⟨23068737065015588284291885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30758316086687451045722513 23068737065015588284291885)
              ·
                refine ⟨8650776399380845606609457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23068737065015588284291885 8650776399380845606609457)
                ·
                  refine ⟨6488082299535634204957093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8650776399380845606609457 6488082299535634204957093)
                  ·
                    refine ⟨1216515431162931413429455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6488082299535634204957093 1216515431162931413429455)
                    ·
                      rfl

theorem cell23_7107466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 3, 2, 4].length) (baseStart_7107466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7107466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7107466 prefixEnd_7107466 := by exact prefixLift 7107466
  have htrace : WordTrace (prefixWord ++ tailWord_7107466) baseStart_7107466 baseEnd_7107466 := by
    simpa [prefixWord, tailWord_7107466, baseEnd_7107466] using wordTrace_append hprefix tailTrace_7107466
  have hstable : (prefixWord ++ tailWord_7107466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7107466).length < 2 ^ (prefixWord ++ tailWord_7107466).sum := by decide
  have hdescent : baseEnd_7107466 < baseStart_7107466 := by decide
  rcases family_descends (prefixWord ++ tailWord_7107466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7107476 : List Nat := [2, 4, 2, 1, 1, 1, 2, 4, 1, 2, 3]
def baseStart_7107476 : Nat := 118140960795 + 7107476 * 2 ^ 59
def prefixEnd_7107476 : Nat := 4983230072969 + 3 ^ 40 * 7107476 * 2
def baseEnd_7107476 : Nat := 3649551428295339201163319

theorem tailTrace_7107476 : CollatzResearch.WordTrace tailWord_7107476 prefixEnd_7107476 3649551428295339201163319 := by
  unfold tailWord_7107476
  simp only [CollatzResearch.WordTrace]
  refine ⟨129615473199417893552779141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172820630932557191403705521 129615473199417893552779141)
  ·
    refine ⟨24302901224890855041146089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129615473199417893552779141 24302901224890855041146089)
    ·
      refine ⟨18227175918668141280859567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24302901224890855041146089 18227175918668141280859567)
      ·
        refine ⟨27340763878002211921289351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18227175918668141280859567 27340763878002211921289351)
        ·
          refine ⟨41011145817003317881934027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27340763878002211921289351 41011145817003317881934027)
          ·
            refine ⟨61516718725504976822901041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41011145817003317881934027 61516718725504976822901041)
            ·
              refine ⟨46137539044128732617175781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61516718725504976822901041 46137539044128732617175781)
              ·
                refine ⟨8650788570774137365720459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46137539044128732617175781 8650788570774137365720459)
                ·
                  refine ⟨12976182856161206048580689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8650788570774137365720459 12976182856161206048580689)
                  ·
                    refine ⟨9732137142120904536435517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12976182856161206048580689 9732137142120904536435517)
                    ·
                      refine ⟨3649551428295339201163319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9732137142120904536435517 3649551428295339201163319)
                      ·
                        rfl

theorem cell23_7107476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_7107476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7107476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7107476 prefixEnd_7107476 := by exact prefixLift 7107476
  have htrace : WordTrace (prefixWord ++ tailWord_7107476) baseStart_7107476 baseEnd_7107476 := by
    simpa [prefixWord, tailWord_7107476, baseEnd_7107476] using wordTrace_append hprefix tailTrace_7107476
  have hstable : (prefixWord ++ tailWord_7107476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7107476).length < 2 ^ (prefixWord ++ tailWord_7107476).sum := by decide
  have hdescent : baseEnd_7107476 < baseStart_7107476 := by decide
  rcases family_descends (prefixWord ++ tailWord_7107476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7107490 : List Nat := [3, 3, 1, 2, 2, 1, 1, 5, 1, 2, 2]
def baseStart_7107490 : Nat := 118140960795 + 7107490 * 2 ^ 59
def prefixEnd_7107490 : Nat := 4983230072969 + 3 ^ 40 * 7107490 * 2
def baseEnd_7107490 : Nat := 3649558617024502146388255

theorem tailTrace_7107490 : CollatzResearch.WordTrace tailWord_7107490 prefixEnd_7107490 3649558617024502146388255 := by
  unfold tailWord_7107490
  simp only [CollatzResearch.WordTrace]
  refine ⟨64807864255196266874141981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172820971347190044997711949 64807864255196266874141981)
  ·
    refine ⟨24302949095698600077803243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64807864255196266874141981 24302949095698600077803243)
    ·
      refine ⟨36454423643547900116704865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24302949095698600077803243 36454423643547900116704865)
      ·
        refine ⟨27340817732660925087528649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36454423643547900116704865 27340817732660925087528649)
        ·
          refine ⟨20505613299495693815646487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27340817732660925087528649 20505613299495693815646487)
          ·
            refine ⟨30758419949243540723469731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20505613299495693815646487 30758419949243540723469731)
            ·
              refine ⟨46137629923865311085204597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30758419949243540723469731 46137629923865311085204597)
              ·
                refine ⟨4325402805362372914237931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46137629923865311085204597 4325402805362372914237931)
                ·
                  refine ⟨6488104208043559371356897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4325402805362372914237931 6488104208043559371356897)
                  ·
                    refine ⟨4866078156032669528517673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6488104208043559371356897 4866078156032669528517673)
                    ·
                      refine ⟨3649558617024502146388255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4866078156032669528517673 3649558617024502146388255)
                      ·
                        rfl

theorem cell23_7107490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 5, 1, 2, 2].length) (baseStart_7107490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7107490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7107490 prefixEnd_7107490 := by exact prefixLift 7107490
  have htrace : WordTrace (prefixWord ++ tailWord_7107490) baseStart_7107490 baseEnd_7107490 := by
    simpa [prefixWord, tailWord_7107490, baseEnd_7107490] using wordTrace_append hprefix tailTrace_7107490
  have hstable : (prefixWord ++ tailWord_7107490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7107490).length < 2 ^ (prefixWord ++ tailWord_7107490).sum := by decide
  have hdescent : baseEnd_7107490 < baseStart_7107490 := by decide
  rcases family_descends (prefixWord ++ tailWord_7107490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7107510 : List Nat := [5, 1, 4, 1, 1, 1, 1, 2, 1, 1, 5]
def baseStart_7107510 : Nat := 118140960795 + 7107510 * 2 ^ 59
def prefixEnd_7107510 : Nat := 4983230072969 + 3 ^ 40 * 7107510 * 2
def baseEnd_7107510 : Nat := 3649568886637592068138163

theorem tailTrace_7107510 : CollatzResearch.WordTrace tailWord_7107510 prefixEnd_7107510 3649568886637592068138163 := by
  unfold tailWord_7107510
  simp only [CollatzResearch.WordTrace]
  refine ⟨16202011655044538182018499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 172821457653808407274863989 16202011655044538182018499)
  ·
    refine ⟨24303017482566807273027749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16202011655044538182018499 24303017482566807273027749)
    ·
      refine ⟨4556815777981276363692703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24303017482566807273027749 4556815777981276363692703)
      ·
        refine ⟨6835223666971914545539055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4556815777981276363692703 6835223666971914545539055)
        ·
          refine ⟨10252835500457871818308583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6835223666971914545539055 10252835500457871818308583)
          ·
            refine ⟨15379253250686807727462875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10252835500457871818308583 15379253250686807727462875)
            ·
              refine ⟨23068879876030211591194313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15379253250686807727462875 23068879876030211591194313)
              ·
                refine ⟨17301659907022658693395735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23068879876030211591194313 17301659907022658693395735)
                ·
                  refine ⟨25952489860533988040093603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17301659907022658693395735 25952489860533988040093603)
                  ·
                    refine ⟨38928734790800982060140405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25952489860533988040093603 38928734790800982060140405)
                    ·
                      refine ⟨3649568886637592068138163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38928734790800982060140405 3649568886637592068138163)
                      ·
                        rfl

theorem cell23_7107510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_7107510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7107510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7107510 prefixEnd_7107510 := by exact prefixLift 7107510
  have htrace : WordTrace (prefixWord ++ tailWord_7107510) baseStart_7107510 baseEnd_7107510 := by
    simpa [prefixWord, tailWord_7107510, baseEnd_7107510] using wordTrace_append hprefix tailTrace_7107510
  have hstable : (prefixWord ++ tailWord_7107510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7107510).length < 2 ^ (prefixWord ++ tailWord_7107510).sum := by decide
  have hdescent : baseEnd_7107510 < baseStart_7107510 := by decide
  rcases family_descends (prefixWord ++ tailWord_7107510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7107549 : List Nat := [1, 4, 3, 1, 2, 1, 1, 1, 1, 3, 5]
def baseStart_7107549 : Nat := 118140960795 + 7107549 * 2 ^ 59
def prefixEnd_7107549 : Nat := 4983230072969 + 3 ^ 40 * 7107549 * 2
def baseEnd_7107549 : Nat := 3649588912383117415550483

theorem tailTrace_7107549 : CollatzResearch.WordTrace tailWord_7107549 prefixEnd_7107549 3649588912383117415550483 := by
  unfold tailWord_7107549
  simp only [CollatzResearch.WordTrace]
  refine ⟨259233608927571320572965701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172822405951714213715310467 259233608927571320572965701)
  ·
    refine ⟨48606301673919622607431069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 259233608927571320572965701 48606301673919622607431069)
    ·
      refine ⟨18227363127719858477786651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48606301673919622607431069 18227363127719858477786651)
      ·
        refine ⟨27341044691579787716679977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18227363127719858477786651 27341044691579787716679977)
        ·
          refine ⟨20505783518684840787509983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27341044691579787716679977 20505783518684840787509983)
          ·
            refine ⟨30758675278027261181264975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20505783518684840787509983 30758675278027261181264975)
            ·
              refine ⟨46138012917040891771897463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30758675278027261181264975 46138012917040891771897463)
              ·
                refine ⟨69207019375561337657846195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46138012917040891771897463 69207019375561337657846195)
                ·
                  refine ⟨103810529063342006486769293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69207019375561337657846195 103810529063342006486769293)
                  ·
                    refine ⟨38928948398753252432538485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 103810529063342006486769293 38928948398753252432538485)
                    ·
                      refine ⟨3649588912383117415550483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38928948398753252432538485 3649588912383117415550483)
                      ·
                        rfl

theorem cell23_7107549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_7107549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7107549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7107549 prefixEnd_7107549 := by exact prefixLift 7107549
  have htrace : WordTrace (prefixWord ++ tailWord_7107549) baseStart_7107549 baseEnd_7107549 := by
    simpa [prefixWord, tailWord_7107549, baseEnd_7107549] using wordTrace_append hprefix tailTrace_7107549
  have hstable : (prefixWord ++ tailWord_7107549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7107549).length < 2 ^ (prefixWord ++ tailWord_7107549).sum := by decide
  have hdescent : baseEnd_7107549 < baseStart_7107549 := by decide
  rcases family_descends (prefixWord ++ tailWord_7107549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7107569 : List Nat := [1, 2, 2, 2, 4, 1, 3, 1, 7]
def baseStart_7107569 : Nat := 118140960795 + 7107569 * 2 ^ 59
def prefixEnd_7107569 : Nat := 4983230072969 + 3 ^ 40 * 7107569 * 2
def baseEnd_7107569 : Nat := 405511020221800815255599

theorem tailTrace_7107569 : CollatzResearch.WordTrace tailWord_7107569 prefixEnd_7107569 405511020221800815255599 := by
  unfold tailWord_7107569
  simp only [CollatzResearch.WordTrace]
  refine ⟨259234338387498863988693761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172822892258332575992462507 259234338387498863988693761)
  ·
    refine ⟨194425753790624147991520321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259234338387498863988693761 194425753790624147991520321)
    ·
      refine ⟨145819315342968110993640241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194425753790624147991520321 145819315342968110993640241)
      ·
        refine ⟨109364486507226083245230181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145819315342968110993640241 109364486507226083245230181)
        ·
          refine ⟨20505841220104890608480659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109364486507226083245230181 20505841220104890608480659)
          ·
            refine ⟨30758761830157335912720989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20505841220104890608480659 30758761830157335912720989)
            ·
              refine ⟨11534535686309000967270371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30758761830157335912720989 11534535686309000967270371)
              ·
                refine ⟨17301803529463501450905557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11534535686309000967270371 17301803529463501450905557)
                ·
                  refine ⟨405511020221800815255599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17301803529463501450905557 405511020221800815255599)
                  ·
                    rfl

theorem cell23_7107569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 1, 7].length) (baseStart_7107569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7107569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7107569 prefixEnd_7107569 := by exact prefixLift 7107569
  have htrace : WordTrace (prefixWord ++ tailWord_7107569) baseStart_7107569 baseEnd_7107569 := by
    simpa [prefixWord, tailWord_7107569, baseEnd_7107569] using wordTrace_append hprefix tailTrace_7107569
  have hstable : (prefixWord ++ tailWord_7107569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7107569).length < 2 ^ (prefixWord ++ tailWord_7107569).sum := by decide
  have hdescent : baseEnd_7107569 < baseStart_7107569 := by decide
  rcases family_descends (prefixWord ++ tailWord_7107569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7107580 : List Nat := [2, 2, 2, 1, 2, 3, 4, 1, 2, 2, 2]
def baseStart_7107580 : Nat := 118140960795 + 7107580 * 2 ^ 59
def prefixEnd_7107580 : Nat := 4983230072969 + 3 ^ 40 * 7107580 * 2
def baseEnd_7107580 : Nat := 3649604830283406794262841

theorem tailTrace_7107580 : CollatzResearch.WordTrace tailWord_7107580 prefixEnd_7107580 3649604830283406794262841 := by
  unfold tailWord_7107580
  simp only [CollatzResearch.WordTrace]
  refine ⟨129617369795229506433672097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172823159726972675244896129 129617369795229506433672097)
  ·
    refine ⟨97213027346422129825254073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129617369795229506433672097 97213027346422129825254073)
    ·
      refine ⟨72909770509816597368940555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97213027346422129825254073 72909770509816597368940555)
      ·
        refine ⟨109364655764724896053410833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72909770509816597368940555 109364655764724896053410833)
        ·
          refine ⟨82023491823543672040058125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109364655764724896053410833 82023491823543672040058125)
          ·
            refine ⟨30758809433828877015021797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82023491823543672040058125 30758809433828877015021797)
            ·
              refine ⟨5767276768842914440316587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30758809433828877015021797 5767276768842914440316587)
              ·
                refine ⟨8650915153264371660474881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5767276768842914440316587 8650915153264371660474881)
                ·
                  refine ⟨6488186364948278745356161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8650915153264371660474881 6488186364948278745356161)
                  ·
                    refine ⟨4866139773711209059017121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6488186364948278745356161 4866139773711209059017121)
                    ·
                      refine ⟨3649604830283406794262841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4866139773711209059017121 3649604830283406794262841)
                      ·
                        rfl

theorem cell23_7107580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 4, 1, 2, 2, 2].length) (baseStart_7107580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7107580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7107580 prefixEnd_7107580 := by exact prefixLift 7107580
  have htrace : WordTrace (prefixWord ++ tailWord_7107580) baseStart_7107580 baseEnd_7107580 := by
    simpa [prefixWord, tailWord_7107580, baseEnd_7107580] using wordTrace_append hprefix tailTrace_7107580
  have hstable : (prefixWord ++ tailWord_7107580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7107580).length < 2 ^ (prefixWord ++ tailWord_7107580).sum := by decide
  have hdescent : baseEnd_7107580 < baseStart_7107580 := by decide
  rcases family_descends (prefixWord ++ tailWord_7107580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7107620 : List Nat := [2, 3, 1, 4, 1, 3, 2, 2, 5]
def baseStart_7107620 : Nat := 118140960795 + 7107620 * 2 ^ 59
def prefixEnd_7107620 : Nat := 4983230072969 + 3 ^ 40 * 7107620 * 2
def baseEnd_7107620 : Nat := 405513929945509626418073

theorem tailTrace_7107620 : CollatzResearch.WordTrace tailWord_7107620 prefixEnd_7107620 405513929945509626418073 := by
  unfold tailWord_7107620
  simp only [CollatzResearch.WordTrace]
  refine ⟨129618099255157049849400157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172824132340209399799200209 129618099255157049849400157)
  ·
    refine ⟨48606787220683893693525059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129618099255157049849400157 48606787220683893693525059)
    ·
      refine ⟨72910180831025840540287589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48606787220683893693525059 72910180831025840540287589)
      ·
        refine ⟨13670658905817345101303923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72910180831025840540287589 13670658905817345101303923)
        ·
          refine ⟨20505988358726017651955885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13670658905817345101303923 20505988358726017651955885)
          ·
            refine ⟨7689745634522256619483457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20505988358726017651955885 7689745634522256619483457)
            ·
              refine ⟨5767309225891692464612593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7689745634522256619483457 5767309225891692464612593)
              ·
                refine ⟨4325481919418769348459445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5767309225891692464612593 4325481919418769348459445)
                ·
                  refine ⟨405513929945509626418073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4325481919418769348459445 405513929945509626418073)
                  ·
                    rfl

theorem cell23_7107620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 2, 2, 5].length) (baseStart_7107620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7107620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7107620 prefixEnd_7107620 := by exact prefixLift 7107620
  have htrace : WordTrace (prefixWord ++ tailWord_7107620) baseStart_7107620 baseEnd_7107620 := by
    simpa [prefixWord, tailWord_7107620, baseEnd_7107620] using wordTrace_append hprefix tailTrace_7107620
  have hstable : (prefixWord ++ tailWord_7107620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7107620).length < 2 ^ (prefixWord ++ tailWord_7107620).sum := by decide
  have hdescent : baseEnd_7107620 < baseStart_7107620 := by decide
  rcases family_descends (prefixWord ++ tailWord_7107620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7107623 : List Nat := [1, 1, 7, 1, 1, 1, 1, 1, 2, 5, 2]
def baseStart_7107623 : Nat := 118140960795 + 7107623 * 2 ^ 59
def prefixEnd_7107623 : Nat := 4983230072969 + 3 ^ 40 * 7107623 * 2
def baseEnd_7107623 : Nat := 3649626909951550126025143

theorem tailTrace_7107623 : CollatzResearch.WordTrace tailWord_7107623 prefixEnd_7107623 3649626909951550126025143 := by
  unfold tailWord_7107623
  simp only [CollatzResearch.WordTrace]
  refine ⟨259236307929303231211159523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172824205286202154140773015 259236307929303231211159523)
  ·
    refine ⟨388854461893954846816739285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259236307929303231211159523 388854461893954846816739285)
    ·
      refine ⟨9113776450639566722267327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 388854461893954846816739285 9113776450639566722267327)
      ·
        refine ⟨13670664675959350083400991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9113776450639566722267327 13670664675959350083400991)
        ·
          refine ⟨20505997013939025125101487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13670664675959350083400991 20505997013939025125101487)
          ·
            refine ⟨30758995520908537687652231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20505997013939025125101487 30758995520908537687652231)
            ·
              refine ⟨46138493281362806531478347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30758995520908537687652231 46138493281362806531478347)
              ·
                refine ⟨69207739922044209797217521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46138493281362806531478347 69207739922044209797217521)
                ·
                  refine ⟨51905804941533157347913141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69207739922044209797217521 51905804941533157347913141)
                  ·
                    refine ⟨4866169213268733501366857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51905804941533157347913141 4866169213268733501366857)
                    ·
                      refine ⟨3649626909951550126025143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4866169213268733501366857 3649626909951550126025143)
                      ·
                        rfl

theorem cell23_7107623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_7107623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7107623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7107623 prefixEnd_7107623 := by exact prefixLift 7107623
  have htrace : WordTrace (prefixWord ++ tailWord_7107623) baseStart_7107623 baseEnd_7107623 := by
    simpa [prefixWord, tailWord_7107623, baseEnd_7107623] using wordTrace_append hprefix tailTrace_7107623
  have hstable : (prefixWord ++ tailWord_7107623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7107623).length < 2 ^ (prefixWord ++ tailWord_7107623).sum := by decide
  have hdescent : baseEnd_7107623 < baseStart_7107623 := by decide
  rcases family_descends (prefixWord ++ tailWord_7107623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7107639 : List Nat := [1, 1, 3, 1, 2, 2, 1, 4, 1, 4, 3]
def baseStart_7107639 : Nat := 118140960795 + 7107639 * 2 ^ 59
def prefixEnd_7107639 : Nat := 4983230072969 + 3 ^ 40 * 7107639 * 2
def baseEnd_7107639 : Nat := 3649635125642022063425069

theorem tailTrace_7107639 : CollatzResearch.WordTrace tailWord_7107639 prefixEnd_7107639 3649635125642022063425069 := by
  unfold tailWord_7107639
  simp only [CollatzResearch.WordTrace]
  refine ⟨259236891497245265943741971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172824594331496843962494647 259236891497245265943741971)
  ·
    refine ⟨388855337245867898915612957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259236891497245265943741971 388855337245867898915612957)
    ·
      refine ⟨145820751467200462093354859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 388855337245867898915612957 145820751467200462093354859)
      ·
        refine ⟨218731127200800693140032289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145820751467200462093354859 218731127200800693140032289)
        ·
          refine ⟨164048345400600519855024217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218731127200800693140032289 164048345400600519855024217)
          ·
            refine ⟨123036259050450389891268163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164048345400600519855024217 123036259050450389891268163)
            ·
              refine ⟨184554388575675584836902245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123036259050450389891268163 184554388575675584836902245)
              ·
                refine ⟨34603947857939172156919171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 184554388575675584836902245 34603947857939172156919171)
                ·
                  refine ⟨51905921786908758235378757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34603947857939172156919171 51905921786908758235378757)
                  ·
                    refine ⟨9732360335045392169133517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51905921786908758235378757 9732360335045392169133517)
                    ·
                      refine ⟨3649635125642022063425069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9732360335045392169133517 3649635125642022063425069)
                      ·
                        rfl

theorem cell23_7107639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 4, 3].length) (baseStart_7107639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7107639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7107639 prefixEnd_7107639 := by exact prefixLift 7107639
  have htrace : WordTrace (prefixWord ++ tailWord_7107639) baseStart_7107639 baseEnd_7107639 := by
    simpa [prefixWord, tailWord_7107639, baseEnd_7107639] using wordTrace_append hprefix tailTrace_7107639
  have hstable : (prefixWord ++ tailWord_7107639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7107639).length < 2 ^ (prefixWord ++ tailWord_7107639).sum := by decide
  have hdescent : baseEnd_7107639 < baseStart_7107639 := by decide
  rcases family_descends (prefixWord ++ tailWord_7107639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7107693 : List Nat := [1, 5, 1, 1, 2, 3, 3, 1, 6]
def baseStart_7107693 : Nat := 118140960795 + 7107693 * 2 ^ 59
def prefixEnd_7107693 : Nat := 4983230072969 + 3 ^ 40 * 7107693 * 2
def baseEnd_7107693 : Nat := 405518094844151650238869

theorem tailTrace_7107693 : CollatzResearch.WordTrace tailWord_7107693 prefixEnd_7107693 405518094844151650238869 := by
  unfold tailWord_7107693
  simp only [CollatzResearch.WordTrace]
  refine ⟨259238861039049633166207733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172825907359366422110805155 259238861039049633166207733)
  ·
    refine ⟨24303643222410903109331975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 259238861039049633166207733 24303643222410903109331975)
    ·
      refine ⟨36455464833616354663997963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24303643222410903109331975 36455464833616354663997963)
      ·
        refine ⟨54683197250424531995996945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36455464833616354663997963 54683197250424531995996945)
        ·
          refine ⟨41012397937818398996997709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54683197250424531995996945 41012397937818398996997709)
          ·
            refine ⟨15379649226681899623874141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41012397937818398996997709 15379649226681899623874141)
            ·
              refine ⟨5767368460005712358952803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15379649226681899623874141 5767368460005712358952803)
              ·
                refine ⟨8651052690008568538429205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5767368460005712358952803 8651052690008568538429205)
                ·
                  refine ⟨405518094844151650238869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8651052690008568538429205 405518094844151650238869)
                  ·
                    rfl

theorem cell23_7107693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 3, 1, 6].length) (baseStart_7107693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7107693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7107693 prefixEnd_7107693 := by exact prefixLift 7107693
  have htrace : WordTrace (prefixWord ++ tailWord_7107693) baseStart_7107693 baseEnd_7107693 := by
    simpa [prefixWord, tailWord_7107693, baseEnd_7107693] using wordTrace_append hprefix tailTrace_7107693
  have hstable : (prefixWord ++ tailWord_7107693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7107693).length < 2 ^ (prefixWord ++ tailWord_7107693).sum := by decide
  have hdescent : baseEnd_7107693 < baseStart_7107693 := by decide
  rcases family_descends (prefixWord ++ tailWord_7107693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7107696 : List Nat := [2, 1, 1, 1, 5, 1, 1, 1, 3, 5, 2]
def baseStart_7107696 : Nat := 118140960795 + 7107696 * 2 ^ 59
def prefixEnd_7107696 : Nat := 4983230072969 + 3 ^ 40 * 7107696 * 2
def baseEnd_7107696 : Nat := 3649664394039328340412307

theorem tailTrace_7107696 : CollatzResearch.WordTrace tailWord_7107696 prefixEnd_7107696 3649664394039328340412307 := by
  unfold tailWord_7107696
  simp only [CollatzResearch.WordTrace]
  refine ⟨129619485229019382339283471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172825980305359176452377961 129619485229019382339283471)
  ·
    refine ⟨194429227843529073508925207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129619485229019382339283471 194429227843529073508925207)
    ·
      refine ⟨291643841765293610263387811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194429227843529073508925207 291643841765293610263387811)
      ·
        refine ⟨437465762647940415395081717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291643841765293610263387811 437465762647940415395081717)
        ·
          refine ⟨41012415248244413943288911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 437465762647940415395081717 41012415248244413943288911)
          ·
            refine ⟨61518622872366620914933367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41012415248244413943288911 61518622872366620914933367)
            ·
              refine ⟨92277934308549931372400051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61518622872366620914933367 92277934308549931372400051)
              ·
                refine ⟨138416901462824897058600077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92277934308549931372400051 138416901462824897058600077)
                ·
                  refine ⟨51906338048559336396975029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 138416901462824897058600077 51906338048559336396975029)
                  ·
                    refine ⟨4866219192052437787216409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51906338048559336396975029 4866219192052437787216409)
                    ·
                      refine ⟨3649664394039328340412307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4866219192052437787216409 3649664394039328340412307)
                      ·
                        rfl

theorem cell23_7107696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 3, 5, 2].length) (baseStart_7107696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7107696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7107696 prefixEnd_7107696 := by exact prefixLift 7107696
  have htrace : WordTrace (prefixWord ++ tailWord_7107696) baseStart_7107696 baseEnd_7107696 := by
    simpa [prefixWord, tailWord_7107696, baseEnd_7107696] using wordTrace_append hprefix tailTrace_7107696
  have hstable : (prefixWord ++ tailWord_7107696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7107696).length < 2 ^ (prefixWord ++ tailWord_7107696).sum := by decide
  have hdescent : baseEnd_7107696 < baseStart_7107696 := by decide
  rcases family_descends (prefixWord ++ tailWord_7107696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7107713 : List Nat := [1, 2, 4, 2, 2, 1, 2, 1, 1, 5, 2]
def baseStart_7107713 : Nat := 118140960795 + 7107713 * 2 ^ 59
def prefixEnd_7107713 : Nat := 4983230072969 + 3 ^ 40 * 7107713 * 2
def baseEnd_7107713 : Nat := 3649673123210454773899729

theorem tailTrace_7107713 : CollatzResearch.WordTrace tailWord_7107713 prefixEnd_7107713 3649673123210454773899729 := by
  unfold tailWord_7107713
  simp only [CollatzResearch.WordTrace]
  refine ⟨259239590498977176581935793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172826393665984784387957195 259239590498977176581935793)
  ·
    refine ⟨194429692874232882436451845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259239590498977176581935793 194429692874232882436451845)
    ·
      refine ⟨36455567413918665456834721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 194429692874232882436451845 36455567413918665456834721)
      ·
        refine ⟨27341675560438999092626041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36455567413918665456834721 27341675560438999092626041)
        ·
          refine ⟨20506256670329249319469531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27341675560438999092626041 20506256670329249319469531)
          ·
            refine ⟨30759385005493873979204297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20506256670329249319469531 30759385005493873979204297)
            ·
              refine ⟨23069538754120405484403223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30759385005493873979204297 23069538754120405484403223)
              ·
                refine ⟨34604308131180608226604835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23069538754120405484403223 34604308131180608226604835)
                ·
                  refine ⟨51906462196770912339907253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34604308131180608226604835 51906462196770912339907253)
                  ·
                    refine ⟨4866230830947273031866305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51906462196770912339907253 4866230830947273031866305)
                    ·
                      refine ⟨3649673123210454773899729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4866230830947273031866305 3649673123210454773899729)
                      ·
                        rfl

theorem cell23_7107713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 5, 2].length) (baseStart_7107713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7107713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7107713 prefixEnd_7107713 := by exact prefixLift 7107713
  have htrace : WordTrace (prefixWord ++ tailWord_7107713) baseStart_7107713 baseEnd_7107713 := by
    simpa [prefixWord, tailWord_7107713, baseEnd_7107713] using wordTrace_append hprefix tailTrace_7107713
  have hstable : (prefixWord ++ tailWord_7107713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7107713).length < 2 ^ (prefixWord ++ tailWord_7107713).sum := by decide
  have hdescent : baseEnd_7107713 < baseStart_7107713 := by decide
  rcases family_descends (prefixWord ++ tailWord_7107713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7107719 : List Nat := [1, 1, 4, 2, 1, 1, 1, 3, 3, 6]
def baseStart_7107719 : Nat := 118140960795 + 7107719 * 2 ^ 59
def prefixEnd_7107719 : Nat := 4983230072969 + 3 ^ 40 * 7107719 * 2
def baseEnd_7107719 : Nat := 1216558734698127250141567

theorem tailTrace_7107719 : CollatzResearch.WordTrace tailWord_7107719 prefixEnd_7107719 1216558734698127250141567 := by
  unfold tailWord_7107719
  simp only [CollatzResearch.WordTrace]
  refine ⟨259239809336955439606654211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172826539557970293071102807 259239809336955439606654211)
  ·
    refine ⟨388859714005433159409981317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259239809336955439606654211 388859714005433159409981317)
    ·
      refine ⟨72911196376018717389371497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 388859714005433159409981317 72911196376018717389371497)
      ·
        refine ⟨54683397282014038042028623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72911196376018717389371497 54683397282014038042028623)
        ·
          refine ⟨82025095923021057063042935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54683397282014038042028623 82025095923021057063042935)
          ·
            refine ⟨123037643884531585594564403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82025095923021057063042935 123037643884531585594564403)
            ·
              refine ⟨184556465826797378391846605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123037643884531585594564403 184556465826797378391846605)
              ·
                refine ⟨69208674685049016896942477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 184556465826797378391846605 69208674685049016896942477)
                ·
                  refine ⟨25953253006893381336353429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69208674685049016896942477 25953253006893381336353429)
                  ·
                    refine ⟨1216558734698127250141567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25953253006893381336353429 1216558734698127250141567)
                    ·
                      rfl

theorem cell23_7107719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 3, 6].length) (baseStart_7107719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7107719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7107719 prefixEnd_7107719 := by exact prefixLift 7107719
  have htrace : WordTrace (prefixWord ++ tailWord_7107719) baseStart_7107719 baseEnd_7107719 := by
    simpa [prefixWord, tailWord_7107719, baseEnd_7107719] using wordTrace_append hprefix tailTrace_7107719
  have hstable : (prefixWord ++ tailWord_7107719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7107719).length < 2 ^ (prefixWord ++ tailWord_7107719).sum := by decide
  have hdescent : baseEnd_7107719 < baseStart_7107719 := by decide
  rcases family_descends (prefixWord ++ tailWord_7107719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7107730 : List Nat := [3, 2, 3, 1, 1, 3, 1, 2, 2, 3, 2]
def baseStart_7107730 : Nat := 118140960795 + 7107730 * 2 ^ 59
def prefixEnd_7107730 : Nat := 4983230072969 + 3 ^ 40 * 7107730 * 2
def baseEnd_7107730 : Nat := 3649681852381581207387151

theorem tailTrace_7107730 : CollatzResearch.WordTrace tailWord_7107730 prefixEnd_7107730 3649681852381581207387151 := by
  unfold tailWord_7107730
  simp only [CollatzResearch.WordTrace]
  refine ⟨64810052634978897121326161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172826807026610392323536429 64810052634978897121326161)
  ·
    refine ⟨48607539476234172840994621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64810052634978897121326161 48607539476234172840994621)
    ·
      refine ⟨18227827303587814815372983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48607539476234172840994621 18227827303587814815372983)
      ·
        refine ⟨27341740955381722223059475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18227827303587814815372983 27341740955381722223059475)
        ·
          refine ⟨41012611433072583334589213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27341740955381722223059475 41012611433072583334589213)
          ·
            refine ⟨15379729287402218750470955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41012611433072583334589213 15379729287402218750470955)
            ·
              refine ⟨23069593931103328125706433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15379729287402218750470955 23069593931103328125706433)
              ·
                refine ⟨17302195448327496094279825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23069593931103328125706433 17302195448327496094279825)
                ·
                  refine ⟨12976646586245622070709869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17302195448327496094279825 12976646586245622070709869)
                  ·
                    refine ⟨4866242469842108276516201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12976646586245622070709869 4866242469842108276516201)
                    ·
                      refine ⟨3649681852381581207387151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4866242469842108276516201 3649681852381581207387151)
                      ·
                        rfl

theorem cell23_7107730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 2, 2, 3, 2].length) (baseStart_7107730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7107730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7107730 prefixEnd_7107730 := by exact prefixLift 7107730
  have htrace : WordTrace (prefixWord ++ tailWord_7107730) baseStart_7107730 baseEnd_7107730 := by
    simpa [prefixWord, tailWord_7107730, baseEnd_7107730] using wordTrace_append hprefix tailTrace_7107730
  have hstable : (prefixWord ++ tailWord_7107730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7107730).length < 2 ^ (prefixWord ++ tailWord_7107730).sum := by decide
  have hdescent : baseEnd_7107730 < baseStart_7107730 := by decide
  rcases family_descends (prefixWord ++ tailWord_7107730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7107749 : List Nat := [1, 3, 1, 2, 1, 4, 1, 10]
def baseStart_7107749 : Nat := 118140960795 + 7107749 * 2 ^ 59
def prefixEnd_7107749 : Nat := 4983230072969 + 3 ^ 40 * 7107749 * 2
def baseEnd_7107749 : Nat := 135173763278296912335169

theorem tailTrace_7107749 : CollatzResearch.WordTrace tailWord_7107749 prefixEnd_7107749 135173763278296912335169 := by
  unfold tailWord_7107749
  simp only [CollatzResearch.WordTrace]
  refine ⟨259240903526846754730246301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172827269017897836486830867 259240903526846754730246301)
  ·
    refine ⟨97215338822567533023842363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259240903526846754730246301 97215338822567533023842363)
    ·
      refine ⟨145823008233851299535763545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97215338822567533023842363 145823008233851299535763545)
      ·
        refine ⟨109367256175388474651822659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145823008233851299535763545 109367256175388474651822659)
        ·
          refine ⟨164050884263082711977733989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109367256175388474651822659 164050884263082711977733989)
          ·
            refine ⟨30759540799328008495825123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 164050884263082711977733989 30759540799328008495825123)
            ·
              refine ⟨46139311198992012743737685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30759540799328008495825123 46139311198992012743737685)
              ·
                refine ⟨135173763278296912335169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 46139311198992012743737685 135173763278296912335169)
                ·
                  rfl

theorem cell23_7107749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 10].length) (baseStart_7107749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7107749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7107749 prefixEnd_7107749 := by exact prefixLift 7107749
  have htrace : WordTrace (prefixWord ++ tailWord_7107749) baseStart_7107749 baseEnd_7107749 := by
    simpa [prefixWord, tailWord_7107749, baseEnd_7107749] using wordTrace_append hprefix tailTrace_7107749
  have hstable : (prefixWord ++ tailWord_7107749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7107749).length < 2 ^ (prefixWord ++ tailWord_7107749).sum := by decide
  have hdescent : baseEnd_7107749 < baseStart_7107749 := by decide
  rcases family_descends (prefixWord ++ tailWord_7107749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7107757 : List Nat := [1, 5, 2, 1, 4, 1, 1, 2, 1, 5]
def baseStart_7107757 : Nat := 118140960795 + 7107757 * 2 ^ 59
def prefixEnd_7107757 : Nat := 4983230072969 + 3 ^ 40 * 7107757 * 2
def baseEnd_7107757 : Nat := 1216565238786417533916509

theorem tailTrace_7107757 : CollatzResearch.WordTrace tailWord_7107757 prefixEnd_7107757 1216565238786417533916509 := by
  unfold tailWord_7107757
  simp only [CollatzResearch.WordTrace]
  refine ⟨259241195310817772096537525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172827463540545181397691683 259241195310817772096537525)
  ·
    refine ⟨24303862060389166134050393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 259241195310817772096537525 24303862060389166134050393)
    ·
      refine ⟨18227896545291874600537795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24303862060389166134050393 18227896545291874600537795)
      ·
        refine ⟨27341844817937811900806693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18227896545291874600537795 27341844817937811900806693)
        ·
          refine ⟨5126595903363339731401255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27341844817937811900806693 5126595903363339731401255)
          ·
            refine ⟨7689893855045009597101883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5126595903363339731401255 7689893855045009597101883)
            ·
              refine ⟨11534840782567514395652825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7689893855045009597101883 11534840782567514395652825)
              ·
                refine ⟨8651130586925635796739619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11534840782567514395652825 8651130586925635796739619)
                ·
                  refine ⟨12976695880388453695109429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8651130586925635796739619 12976695880388453695109429)
                  ·
                    refine ⟨1216565238786417533916509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12976695880388453695109429 1216565238786417533916509)
                    ·
                      rfl

theorem cell23_7107757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_7107757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7107757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7107757 prefixEnd_7107757 := by exact prefixLift 7107757
  have htrace : WordTrace (prefixWord ++ tailWord_7107757) baseStart_7107757 baseEnd_7107757 := by
    simpa [prefixWord, tailWord_7107757, baseEnd_7107757] using wordTrace_append hprefix tailTrace_7107757
  have hstable : (prefixWord ++ tailWord_7107757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7107757).length < 2 ^ (prefixWord ++ tailWord_7107757).sum := by decide
  have hdescent : baseEnd_7107757 < baseStart_7107757 := by decide
  rcases family_descends (prefixWord ++ tailWord_7107757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7107763 : List Nat := [1, 1, 1, 2, 3, 2, 5, 2, 1, 2, 3]
def baseStart_7107763 : Nat := 118140960795 + 7107763 * 2 ^ 59
def prefixEnd_7107763 : Nat := 4983230072969 + 3 ^ 40 * 7107763 * 2
def baseEnd_7107763 : Nat := 3649698797243179578274499

theorem tailTrace_7107763 : CollatzResearch.WordTrace tailWord_7107763 prefixEnd_7107763 3649698797243179578274499 := by
  unfold tailWord_7107763
  simp only [CollatzResearch.WordTrace]
  refine ⟨259241414148796035121255943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172827609432530690080837295 259241414148796035121255943)
  ·
    refine ⟨388862121223194052681883915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259241414148796035121255943 388862121223194052681883915)
    ·
      refine ⟨583293181834791079022825873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388862121223194052681883915 583293181834791079022825873)
      ·
        refine ⟨437469886376093309267119405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 583293181834791079022825873 437469886376093309267119405)
        ·
          refine ⟨164051207391034990975169777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 437469886376093309267119405 164051207391034990975169777)
          ·
            refine ⟨123038405543276243231377333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164051207391034990975169777 123038405543276243231377333)
            ·
              refine ⟨11534850519682147802941625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 123038405543276243231377333 11534850519682147802941625)
              ·
                refine ⟨8651137889761610852206219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11534850519682147802941625 8651137889761610852206219)
                ·
                  refine ⟨12976706834642416278309329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8651137889761610852206219 12976706834642416278309329)
                  ·
                    refine ⟨9732530125981812208731997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12976706834642416278309329 9732530125981812208731997)
                    ·
                      refine ⟨3649698797243179578274499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9732530125981812208731997 3649698797243179578274499)
                      ·
                        rfl

theorem cell23_7107763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 2, 1, 2, 3].length) (baseStart_7107763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7107763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7107763 prefixEnd_7107763 := by exact prefixLift 7107763
  have htrace : WordTrace (prefixWord ++ tailWord_7107763) baseStart_7107763 baseEnd_7107763 := by
    simpa [prefixWord, tailWord_7107763, baseEnd_7107763] using wordTrace_append hprefix tailTrace_7107763
  have hstable : (prefixWord ++ tailWord_7107763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7107763).length < 2 ^ (prefixWord ++ tailWord_7107763).sum := by decide
  have hdescent : baseEnd_7107763 < baseStart_7107763 := by decide
  rcases family_descends (prefixWord ++ tailWord_7107763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7107777 : List Nat := [1, 2, 6, 1, 1, 2, 3, 1, 1, 1, 4]
def baseStart_7107777 : Nat := 118140960795 + 7107777 * 2 ^ 59
def prefixEnd_7107777 : Nat := 4983230072969 + 3 ^ 40 * 7107777 * 2
def baseEnd_7107777 : Nat := 3649705985972342523499435

theorem tailTrace_7107777 : CollatzResearch.WordTrace tailWord_7107777 prefixEnd_7107777 3649705985972342523499435 := by
  unfold tailWord_7107777
  simp only [CollatzResearch.WordTrace]
  refine ⟨259241924770745315512265585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172827949847163543674843723 259241924770745315512265585)
  ·
    refine ⟨194431443578058986634199189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259241924770745315512265585 194431443578058986634199189)
    ·
      refine ⟨9113973917721514998478087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 194431443578058986634199189 9113973917721514998478087)
      ·
        refine ⟨13670960876582272497717131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9113973917721514998478087 13670960876582272497717131)
        ·
          refine ⟨20506441314873408746575697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13670960876582272497717131 20506441314873408746575697)
          ·
            refine ⟨15379830986155056559931773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20506441314873408746575697 15379830986155056559931773)
            ·
              refine ⟨5767436619808146209974415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15379830986155056559931773 5767436619808146209974415)
              ·
                refine ⟨8651154929712219314961623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5767436619808146209974415 8651154929712219314961623)
                ·
                  refine ⟨12976732394568328972442435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8651154929712219314961623 12976732394568328972442435)
                  ·
                    refine ⟨19465098591852493458663653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12976732394568328972442435 19465098591852493458663653)
                    ·
                      refine ⟨3649705985972342523499435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19465098591852493458663653 3649705985972342523499435)
                      ·
                        rfl

theorem cell23_7107777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_7107777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7107777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7107777 prefixEnd_7107777 := by exact prefixLift 7107777
  have htrace : WordTrace (prefixWord ++ tailWord_7107777) baseStart_7107777 baseEnd_7107777 := by
    simpa [prefixWord, tailWord_7107777, baseEnd_7107777] using wordTrace_append hprefix tailTrace_7107777
  have hstable : (prefixWord ++ tailWord_7107777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7107777).length < 2 ^ (prefixWord ++ tailWord_7107777).sum := by decide
  have hdescent : baseEnd_7107777 < baseStart_7107777 := by decide
  rcases family_descends (prefixWord ++ tailWord_7107777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7107780 : List Nat := [2, 3, 3, 1, 3, 2, 1, 1, 1, 1, 5]
def baseStart_7107780 : Nat := 118140960795 + 7107780 * 2 ^ 59
def prefixEnd_7107780 : Nat := 4983230072969 + 3 ^ 40 * 7107780 * 2
def baseEnd_7107780 : Nat := 3649707526414306011761921

theorem tailTrace_7107780 : CollatzResearch.WordTrace tailWord_7107780 prefixEnd_7107780 3649707526414306011761921 := by
  unfold tailWord_7107780
  simp only [CollatzResearch.WordTrace]
  refine ⟨129621017094867223512312397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172828022793156298016416529 129621017094867223512312397)
  ·
    refine ⟨48607881410575208817117149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129621017094867223512312397 48607881410575208817117149)
    ·
      refine ⟨18227955528965703306418931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48607881410575208817117149 18227955528965703306418931)
      ·
        refine ⟨27341933293448554959628397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18227955528965703306418931 27341933293448554959628397)
        ·
          refine ⟨10253224985043208109860649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27341933293448554959628397 10253224985043208109860649)
          ·
            refine ⟨7689918738782406082395487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10253224985043208109860649 7689918738782406082395487)
            ·
              refine ⟨11534878108173609123593231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7689918738782406082395487 11534878108173609123593231)
              ·
                refine ⟨17302317162260413685389847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11534878108173609123593231 17302317162260413685389847)
                ·
                  refine ⟨25953475743390620528084771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17302317162260413685389847 25953475743390620528084771)
                  ·
                    refine ⟨38930213615085930792127157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25953475743390620528084771 38930213615085930792127157)
                    ·
                      refine ⟨3649707526414306011761921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38930213615085930792127157 3649707526414306011761921)
                      ·
                        rfl

theorem cell23_7107780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_7107780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7107780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7107780 prefixEnd_7107780 := by exact prefixLift 7107780
  have htrace : WordTrace (prefixWord ++ tailWord_7107780) baseStart_7107780 baseEnd_7107780 := by
    simpa [prefixWord, tailWord_7107780, baseEnd_7107780] using wordTrace_append hprefix tailTrace_7107780
  have hstable : (prefixWord ++ tailWord_7107780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7107780).length < 2 ^ (prefixWord ++ tailWord_7107780).sum := by decide
  have hdescent : baseEnd_7107780 < baseStart_7107780 := by decide
  rcases family_descends (prefixWord ++ tailWord_7107780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7107816 : List Nat := [2, 1, 4, 1, 2, 1, 1, 2, 2, 3, 4]
def baseStart_7107816 : Nat := 118140960795 + 7107816 * 2 ^ 59
def prefixEnd_7107816 : Nat := 4983230072969 + 3 ^ 40 * 7107816 * 2
def baseEnd_7107816 : Nat := 3649726011717867870911755

theorem tailTrace_7107816 : CollatzResearch.WordTrace tailWord_7107816 prefixEnd_7107816 3649726011717867870911755 := by
  unfold tailWord_7107816
  simp only [CollatzResearch.WordTrace]
  refine ⟨129621673608802012586467651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172828898145069350115290201 129621673608802012586467651)
  ·
    refine ⟨194432510413203018879701477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129621673608802012586467651 194432510413203018879701477)
    ·
      refine ⟨36456095702475566039944027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 194432510413203018879701477 36456095702475566039944027)
      ·
        refine ⟨54684143553713349059916041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36456095702475566039944027 54684143553713349059916041)
        ·
          refine ⟨41013107665285011794937031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54684143553713349059916041 41013107665285011794937031)
          ·
            refine ⟨61519661497927517692405547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41013107665285011794937031 61519661497927517692405547)
            ·
              refine ⟨92279492246891276538608321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61519661497927517692405547 92279492246891276538608321)
              ·
                refine ⟨69209619185168457403956241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92279492246891276538608321 69209619185168457403956241)
                ·
                  refine ⟨51907214388876343052967181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69209619185168457403956241 51907214388876343052967181)
                  ·
                    refine ⟨19465205395828628644862693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51907214388876343052967181 19465205395828628644862693)
                    ·
                      refine ⟨3649726011717867870911755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19465205395828628644862693 3649726011717867870911755)
                      ·
                        rfl

theorem cell23_7107816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_7107816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7107816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7107816 prefixEnd_7107816 := by exact prefixLift 7107816
  have htrace : WordTrace (prefixWord ++ tailWord_7107816) baseStart_7107816 baseEnd_7107816 := by
    simpa [prefixWord, tailWord_7107816, baseEnd_7107816] using wordTrace_append hprefix tailTrace_7107816
  have hstable : (prefixWord ++ tailWord_7107816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7107816).length < 2 ^ (prefixWord ++ tailWord_7107816).sum := by decide
  have hdescent : baseEnd_7107816 < baseStart_7107816 := by decide
  rcases family_descends (prefixWord ++ tailWord_7107816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7107828 : List Nat := [2, 6, 1, 2, 2, 1, 2, 1, 1, 1, 4]
def baseStart_7107828 : Nat := 118140960795 + 7107828 * 2 ^ 59
def prefixEnd_7107828 : Nat := 4983230072969 + 3 ^ 40 * 7107828 * 2
def baseEnd_7107828 : Nat := 3649732173485721823961701

theorem tailTrace_7107828 : CollatzResearch.WordTrace tailWord_7107828 prefixEnd_7107828 3649732173485721823961701 := by
  unfold tailWord_7107828
  simp only [CollatzResearch.WordTrace]
  refine ⟨129621892446780275611186069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172829189929040367481581425 129621892446780275611186069)
  ·
    refine ⟨6076026208442825419274347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 129621892446780275611186069 6076026208442825419274347)
    ·
      refine ⟨9114039312664238128911521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6076026208442825419274347 9114039312664238128911521)
      ·
        refine ⟨6835529484498178596683641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9114039312664238128911521 6835529484498178596683641)
        ·
          refine ⟨5126647113373633947512731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6835529484498178596683641 5126647113373633947512731)
          ·
            refine ⟨7689970670060450921269097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5126647113373633947512731 7689970670060450921269097)
            ·
              refine ⟨5767478002545338190951823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7689970670060450921269097 5767478002545338190951823)
              ·
                refine ⟨8651217003818007286427735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5767478002545338190951823 8651217003818007286427735)
                ·
                  refine ⟨12976825505727010929641603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8651217003818007286427735 12976825505727010929641603)
                  ·
                    refine ⟨19465238258590516394462405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12976825505727010929641603 19465238258590516394462405)
                    ·
                      refine ⟨3649732173485721823961701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19465238258590516394462405 3649732173485721823961701)
                      ·
                        rfl

theorem cell23_7107828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_7107828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7107828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7107828 prefixEnd_7107828 := by exact prefixLift 7107828
  have htrace : WordTrace (prefixWord ++ tailWord_7107828) baseStart_7107828 baseEnd_7107828 := by
    simpa [prefixWord, tailWord_7107828, baseEnd_7107828] using wordTrace_append hprefix tailTrace_7107828
  have hstable : (prefixWord ++ tailWord_7107828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7107828).length < 2 ^ (prefixWord ++ tailWord_7107828).sum := by decide
  have hdescent : baseEnd_7107828 < baseStart_7107828 := by decide
  rcases family_descends (prefixWord ++ tailWord_7107828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7107833 : List Nat := [1, 2, 1, 3, 1, 1, 3, 4, 1, 4, 2]
def baseStart_7107833 : Nat := 118140960795 + 7107833 * 2 ^ 59
def prefixEnd_7107833 : Nat := 4983230072969 + 3 ^ 40 * 7107833 * 2
def baseEnd_7107833 : Nat := 3649734740888994304399177

theorem tailTrace_7107833 : CollatzResearch.WordTrace tailWord_7107833 prefixEnd_7107833 3649734740888994304399177 := by
  unfold tailWord_7107833
  simp only [CollatzResearch.WordTrace]
  refine ⟨259243967258542437076304153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172829311505694958050869435 259243967258542437076304153)
  ·
    refine ⟨194432975443906827807228115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259243967258542437076304153 194432975443906827807228115)
    ·
      refine ⟨291649463165860241710842173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194432975443906827807228115 291649463165860241710842173)
      ·
        refine ⟨109368548687197590641565815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 291649463165860241710842173 109368548687197590641565815)
        ·
          refine ⟨164052823030796385962348723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109368548687197590641565815 164052823030796385962348723)
          ·
            refine ⟨246079234546194578943523085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164052823030796385962348723 246079234546194578943523085)
            ·
              refine ⟨92279712954822967103821157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 246079234546194578943523085 92279712954822967103821157)
              ·
                refine ⟨17302446179029306331966467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92279712954822967103821157 17302446179029306331966467)
                ·
                  refine ⟨25953669268543959497949701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17302446179029306331966467 25953669268543959497949701)
                  ·
                    refine ⟨4866312987851992405865569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25953669268543959497949701 4866312987851992405865569)
                    ·
                      refine ⟨3649734740888994304399177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4866312987851992405865569 3649734740888994304399177)
                      ·
                        rfl

theorem cell23_7107833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 4, 1, 4, 2].length) (baseStart_7107833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7107833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7107833 prefixEnd_7107833 := by exact prefixLift 7107833
  have htrace : WordTrace (prefixWord ++ tailWord_7107833) baseStart_7107833 baseEnd_7107833 := by
    simpa [prefixWord, tailWord_7107833, baseEnd_7107833] using wordTrace_append hprefix tailTrace_7107833
  have hstable : (prefixWord ++ tailWord_7107833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7107833).length < 2 ^ (prefixWord ++ tailWord_7107833).sum := by decide
  have hdescent : baseEnd_7107833 < baseStart_7107833 := by decide
  rcases family_descends (prefixWord ++ tailWord_7107833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7107890 : List Nat := [3, 2, 1, 1, 4, 1, 3, 3, 5]
def baseStart_7107890 : Nat := 118140960795 + 7107890 * 2 ^ 59
def prefixEnd_7107890 : Nat := 4983230072969 + 3 ^ 40 * 7107890 * 2
def baseEnd_7107890 : Nat := 405529334365144509042935

theorem tailTrace_7107890 : CollatzResearch.WordTrace tailWord_7107890 prefixEnd_7107890 405529334365144509042935 := by
  unfold tailWord_7107890
  simp only [CollatzResearch.WordTrace]
  refine ⟨64811511554833983952782281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172830697479557290540752749 64811511554833983952782281)
  ·
    refine ⟨48608633666125487964586711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64811511554833983952782281 48608633666125487964586711)
    ·
      refine ⟨72912950499188231946880067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48608633666125487964586711 72912950499188231946880067)
      ·
        refine ⟨109369425748782347920320101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72912950499188231946880067 109369425748782347920320101)
        ·
          refine ⟨20506767327896690235060019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109369425748782347920320101 20506767327896690235060019)
          ·
            refine ⟨30760150991845035352590029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20506767327896690235060019 30760150991845035352590029)
            ·
              refine ⟨11535056621941888257221261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30760150991845035352590029 11535056621941888257221261)
              ·
                refine ⟨4325646233228208096457973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11535056621941888257221261 4325646233228208096457973)
                ·
                  refine ⟨405529334365144509042935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4325646233228208096457973 405529334365144509042935)
                  ·
                    rfl

theorem cell23_7107890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 3, 5].length) (baseStart_7107890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7107890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7107890 prefixEnd_7107890 := by exact prefixLift 7107890
  have htrace : WordTrace (prefixWord ++ tailWord_7107890) baseStart_7107890 baseEnd_7107890 := by
    simpa [prefixWord, tailWord_7107890, baseEnd_7107890] using wordTrace_append hprefix tailTrace_7107890
  have hstable : (prefixWord ++ tailWord_7107890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7107890).length < 2 ^ (prefixWord ++ tailWord_7107890).sum := by decide
  have hdescent : baseEnd_7107890 < baseStart_7107890 := by decide
  rcases family_descends (prefixWord ++ tailWord_7107890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7107896 : List Nat := [2, 1, 2, 1, 3, 1, 1, 4, 1, 2, 5]
def baseStart_7107896 : Nat := 118140960795 + 7107896 * 2 ^ 59
def prefixEnd_7107896 : Nat := 4983230072969 + 3 ^ 40 * 7107896 * 2
def baseEnd_7107896 : Nat := 3649767090170227557911387

theorem tailTrace_7107896 : CollatzResearch.WordTrace tailWord_7107896 prefixEnd_7107896 3649767090170227557911387 := by
  unfold tailWord_7107896
  simp only [CollatzResearch.WordTrace]
  refine ⟨129623132528657099417923771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172830843371542799223898361 129623132528657099417923771)
  ·
    refine ⟨194434698792985649126885657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129623132528657099417923771 194434698792985649126885657)
    ·
      refine ⟨145826024094739236845164243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194434698792985649126885657 145826024094739236845164243)
      ·
        refine ⟨218739036142108855267746365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145826024094739236845164243 218739036142108855267746365)
        ·
          refine ⟨82027138553290820725404887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218739036142108855267746365 82027138553290820725404887)
          ·
            refine ⟨123040707829936231088107331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82027138553290820725404887 123040707829936231088107331)
            ·
              refine ⟨184561061744904346632160997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123040707829936231088107331 184561061744904346632160997)
              ·
                refine ⟨34605199077169564993530187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 184561061744904346632160997 34605199077169564993530187)
                ·
                  refine ⟨51907798615754347490295281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34605199077169564993530187 51907798615754347490295281)
                  ·
                    refine ⟨38930848961815760617721461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51907798615754347490295281 38930848961815760617721461)
                    ·
                      refine ⟨3649767090170227557911387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38930848961815760617721461 3649767090170227557911387)
                      ·
                        rfl

theorem cell23_7107896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 1, 2, 5].length) (baseStart_7107896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7107896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7107896 prefixEnd_7107896 := by exact prefixLift 7107896
  have htrace : WordTrace (prefixWord ++ tailWord_7107896) baseStart_7107896 baseEnd_7107896 := by
    simpa [prefixWord, tailWord_7107896, baseEnd_7107896] using wordTrace_append hprefix tailTrace_7107896
  have hstable : (prefixWord ++ tailWord_7107896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7107896).length < 2 ^ (prefixWord ++ tailWord_7107896).sum := by decide
  have hdescent : baseEnd_7107896 < baseStart_7107896 := by decide
  rcases family_descends (prefixWord ++ tailWord_7107896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7107903 : List Nat := [1, 1, 2, 2, 4, 3, 1, 2, 2, 5]
def baseStart_7107903 : Nat := 118140960795 + 7107903 * 2 ^ 59
def prefixEnd_7107903 : Nat := 4983230072969 + 3 ^ 40 * 7107903 * 2
def baseEnd_7107903 : Nat := 1216590228178269676841285

theorem tailTrace_7107903 : CollatzResearch.WordTrace tailWord_7107903 prefixEnd_7107903 1216590228178269676841285 := by
  unfold tailWord_7107903
  simp only [CollatzResearch.WordTrace]
  refine ⟨259246520368288839031352363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172831013578859226020901575 259246520368288839031352363)
  ·
    refine ⟨388869780552433258547028545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259246520368288839031352363 388869780552433258547028545)
    ·
      refine ⟨291652335414324943910271409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 388869780552433258547028545 291652335414324943910271409)
      ·
        refine ⟨218739251560743707932703557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291652335414324943910271409 218739251560743707932703557)
        ·
          refine ⟨41013609667639445237381917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 218739251560743707932703557 41013609667639445237381917)
          ·
            refine ⟨15380103625364791964018219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41013609667639445237381917 15380103625364791964018219)
            ·
              refine ⟨23070155438047187946027329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15380103625364791964018219 23070155438047187946027329)
              ·
                refine ⟨17302616578535390959520497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23070155438047187946027329 17302616578535390959520497)
                ·
                  refine ⟨12976962433901543219640373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17302616578535390959520497 12976962433901543219640373)
                  ·
                    refine ⟨1216590228178269676841285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12976962433901543219640373 1216590228178269676841285)
                    ·
                      rfl

theorem cell23_7107903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 2, 2, 5].length) (baseStart_7107903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7107903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7107903 prefixEnd_7107903 := by exact prefixLift 7107903
  have htrace : WordTrace (prefixWord ++ tailWord_7107903) baseStart_7107903 baseEnd_7107903 := by
    simpa [prefixWord, tailWord_7107903, baseEnd_7107903] using wordTrace_append hprefix tailTrace_7107903
  have hstable : (prefixWord ++ tailWord_7107903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7107903).length < 2 ^ (prefixWord ++ tailWord_7107903).sum := by decide
  have hdescent : baseEnd_7107903 < baseStart_7107903 := by decide
  rcases family_descends (prefixWord ++ tailWord_7107903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7107923 : List Nat := [1, 1, 1, 2, 1, 1, 6, 1, 1, 6, 2]
def baseStart_7107923 : Nat := 118140960795 + 7107923 * 2 ^ 59
def prefixEnd_7107923 : Nat := 4983230072969 + 3 ^ 40 * 7107923 * 2
def baseEnd_7107923 : Nat := 3649780954147898952273763

theorem tailTrace_7107923 : CollatzResearch.WordTrace tailWord_7107923 prefixEnd_7107923 3649780954147898952273763 := by
  unfold tailWord_7107923
  simp only [CollatzResearch.WordTrace]
  refine ⟨259247249828216382447080423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172831499885477588298053615 259247249828216382447080423)
  ·
    refine ⟨388870874742324573670620635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259247249828216382447080423 388870874742324573670620635)
    ·
      refine ⟨583306312113486860505930953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388870874742324573670620635 583306312113486860505930953)
      ·
        refine ⟨437479734085115145379448215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 583306312113486860505930953 437479734085115145379448215)
        ·
          refine ⟨656219601127672718069172323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 437479734085115145379448215 656219601127672718069172323)
          ·
            refine ⟨984329401691509077103758485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 656219601127672718069172323 984329401691509077103758485)
            ·
              refine ⟨46140440704289487989238679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 984329401691509077103758485 46140440704289487989238679)
              ·
                refine ⟨69210661056434231983858019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46140440704289487989238679 69210661056434231983858019)
                ·
                  refine ⟨103815991584651347975787029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69210661056434231983858019 103815991584651347975787029)
                  ·
                    refine ⟨4866374605530531936365017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 103815991584651347975787029 4866374605530531936365017)
                    ·
                      refine ⟨3649780954147898952273763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4866374605530531936365017 3649780954147898952273763)
                      ·
                        rfl

theorem cell23_7107923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 6, 2].length) (baseStart_7107923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7107923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7107923 prefixEnd_7107923 := by exact prefixLift 7107923
  have htrace : WordTrace (prefixWord ++ tailWord_7107923) baseStart_7107923 baseEnd_7107923 := by
    simpa [prefixWord, tailWord_7107923, baseEnd_7107923] using wordTrace_append hprefix tailTrace_7107923
  have hstable : (prefixWord ++ tailWord_7107923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7107923).length < 2 ^ (prefixWord ++ tailWord_7107923).sum := by decide
  have hdescent : baseEnd_7107923 < baseStart_7107923 := by decide
  rcases family_descends (prefixWord ++ tailWord_7107923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7107940 : List Nat := [2, 3, 1, 1, 3, 3, 2, 1, 2, 1, 4]
def baseStart_7107940 : Nat := 118140960795 + 7107940 * 2 ^ 59
def prefixEnd_7107940 : Nat := 4983230072969 + 3 ^ 40 * 7107940 * 2
def baseEnd_7107940 : Nat := 3649789683319025385761185

theorem tailTrace_7107940 : CollatzResearch.WordTrace tailWord_7107940 prefixEnd_7107940 3649789683319025385761185 := by
  unfold tailWord_7107940
  simp only [CollatzResearch.WordTrace]
  refine ⟨129623934934577397175224637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172831913246103196233632849 129623934934577397175224637)
  ·
    refine ⟨48608975600466523940709239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129623934934577397175224637 48608975600466523940709239)
    ·
      refine ⟨72913463400699785911063859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48608975600466523940709239 72913463400699785911063859)
      ·
        refine ⟨109370195101049678866595789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72913463400699785911063859 109370195101049678866595789)
        ·
          refine ⟨41013823162893629574973421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109370195101049678866595789 41013823162893629574973421)
          ·
            refine ⟨15380183686085111090615033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41013823162893629574973421 15380183686085111090615033)
            ·
              refine ⟨11535137764563833317961275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15380183686085111090615033 11535137764563833317961275)
              ·
                refine ⟨17302706646845749976941913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11535137764563833317961275 17302706646845749976941913)
                ·
                  refine ⟨12977029985134312482706435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17302706646845749976941913 12977029985134312482706435)
                  ·
                    refine ⟨19465544977701468724059653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12977029985134312482706435 19465544977701468724059653)
                    ·
                      refine ⟨3649789683319025385761185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19465544977701468724059653 3649789683319025385761185)
                      ·
                        rfl

theorem cell23_7107940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 1, 2, 1, 4].length) (baseStart_7107940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7107940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7107940 prefixEnd_7107940 := by exact prefixLift 7107940
  have htrace : WordTrace (prefixWord ++ tailWord_7107940) baseStart_7107940 baseEnd_7107940 := by
    simpa [prefixWord, tailWord_7107940, baseEnd_7107940] using wordTrace_append hprefix tailTrace_7107940
  have hstable : (prefixWord ++ tailWord_7107940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7107940).length < 2 ^ (prefixWord ++ tailWord_7107940).sum := by decide
  have hdescent : baseEnd_7107940 < baseStart_7107940 := by decide
  rcases family_descends (prefixWord ++ tailWord_7107940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7107963 : List Nat := [1, 1, 1, 1, 1, 6, 4, 2, 6]
def baseStart_7107963 : Nat := 118140960795 + 7107963 * 2 ^ 59
def prefixEnd_7107963 : Nat := 4983230072969 + 3 ^ 40 * 7107963 * 2
def baseEnd_7107963 : Nat := 405533499263786532863731

theorem tailTrace_7107963 : CollatzResearch.WordTrace tailWord_7107963 prefixEnd_7107963 405533499263786532863731 := by
  unfold tailWord_7107963
  simp only [CollatzResearch.WordTrace]
  refine ⟨259248708748071469278536543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172832472498714312852357695 259248708748071469278536543)
  ·
    refine ⟨388873063122107203917804815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259248708748071469278536543 388873063122107203917804815)
    ·
      refine ⟨583309594683160805876707223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388873063122107203917804815 583309594683160805876707223)
      ·
        refine ⟨874964392024741208815060835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 583309594683160805876707223 874964392024741208815060835)
        ·
          refine ⟨1312446588037111813222591253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 874964392024741208815060835 1312446588037111813222591253)
          ·
            refine ⟨61520933814239616244808965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1312446588037111813222591253 61520933814239616244808965)
            ·
              refine ⟨11535175090169928045901681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61520933814239616244808965 11535175090169928045901681)
              ·
                refine ⟨8651381317627446034426261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11535175090169928045901681 8651381317627446034426261)
                ·
                  refine ⟨405533499263786532863731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8651381317627446034426261 405533499263786532863731)
                  ·
                    rfl

theorem cell23_7107963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 2, 6].length) (baseStart_7107963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7107963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7107963 prefixEnd_7107963 := by exact prefixLift 7107963
  have htrace : WordTrace (prefixWord ++ tailWord_7107963) baseStart_7107963 baseEnd_7107963 := by
    simpa [prefixWord, tailWord_7107963, baseEnd_7107963] using wordTrace_append hprefix tailTrace_7107963
  have hstable : (prefixWord ++ tailWord_7107963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7107963).length < 2 ^ (prefixWord ++ tailWord_7107963).sum := by decide
  have hdescent : baseEnd_7107963 < baseStart_7107963 := by decide
  rcases family_descends (prefixWord ++ tailWord_7107963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7107993 : List Nat := [1, 2, 1, 2, 1, 5, 2, 1, 3, 5]
def baseStart_7107993 : Nat := 118140960795 + 7107993 * 2 ^ 59
def prefixEnd_7107993 : Nat := 4983230072969 + 3 ^ 40 * 7107993 * 2
def baseEnd_7107993 : Nat := 1216605632597904559466147

theorem tailTrace_7107993 : CollatzResearch.WordTrace tailWord_7107993 prefixEnd_7107993 1216605632597904559466147 := by
  unfold tailWord_7107993
  simp only [CollatzResearch.WordTrace]
  refine ⟨259249802937962784402128633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172833201958641856268085755 259249802937962784402128633)
  ·
    refine ⟨194437352203472088301596475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259249802937962784402128633 194437352203472088301596475)
    ·
      refine ⟨291656028305208132452394713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194437352203472088301596475 291656028305208132452394713)
      ·
        refine ⟨218742021228906099339296035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291656028305208132452394713 218742021228906099339296035)
        ·
          refine ⟨328113031843359149008944053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218742021228906099339296035 328113031843359149008944053)
          ·
            refine ⟨30760596735314920219588505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 328113031843359149008944053 30760596735314920219588505)
            ·
              refine ⟨23070447551486190164691379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30760596735314920219588505 23070447551486190164691379)
              ·
                refine ⟨34605671327229285247037069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23070447551486190164691379 34605671327229285247037069)
                ·
                  refine ⟨12977126747710981967638901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34605671327229285247037069 12977126747710981967638901)
                  ·
                    refine ⟨1216605632597904559466147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12977126747710981967638901 1216605632597904559466147)
                    ·
                      rfl

theorem cell23_7107993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 3, 5].length) (baseStart_7107993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7107993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7107993 prefixEnd_7107993 := by exact prefixLift 7107993
  have htrace : WordTrace (prefixWord ++ tailWord_7107993) baseStart_7107993 baseEnd_7107993 := by
    simpa [prefixWord, tailWord_7107993, baseEnd_7107993] using wordTrace_append hprefix tailTrace_7107993
  have hstable : (prefixWord ++ tailWord_7107993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7107993).length < 2 ^ (prefixWord ++ tailWord_7107993).sum := by decide
  have hdescent : baseEnd_7107993 < baseStart_7107993 := by decide
  rcases family_descends (prefixWord ++ tailWord_7107993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7108000 : List Nat := [2, 1, 1, 4, 1, 2, 3, 1, 1, 5, 2]
def baseStart_7108000 : Nat := 118140960795 + 7108000 * 2 ^ 59
def prefixEnd_7108000 : Nat := 4983230072969 + 3 ^ 40 * 7108000 * 2
def baseEnd_7108000 : Nat := 3649820492158295151010909

theorem tailTrace_7108000 : CollatzResearch.WordTrace tailWord_7108000 prefixEnd_7108000 3649820492158295151010909 := by
  unfold tailWord_7108000
  simp only [CollatzResearch.WordTrace]
  refine ⟨129625029124468712298816727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172833372165958283065088969 129625029124468712298816727)
  ·
    refine ⟨194437543686703068448225091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129625029124468712298816727 194437543686703068448225091)
    ·
      refine ⟨291656315530054602672337637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194437543686703068448225091 291656315530054602672337637)
      ·
        refine ⟨54685559161885238001063307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 291656315530054602672337637 54685559161885238001063307)
        ·
          refine ⟨82028338742827857001594961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54685559161885238001063307 82028338742827857001594961)
          ·
            refine ⟨61521254057120892751196221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82028338742827857001594961 61521254057120892751196221)
            ·
              refine ⟨23070470271420334781698583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61521254057120892751196221 23070470271420334781698583)
              ·
                refine ⟨34605705407130502172547875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23070470271420334781698583 34605705407130502172547875)
                ·
                  refine ⟨51908558110695753258821813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34605705407130502172547875 51908558110695753258821813)
                  ·
                    refine ⟨4866427322877726868014545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51908558110695753258821813 4866427322877726868014545)
                    ·
                      refine ⟨3649820492158295151010909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4866427322877726868014545 3649820492158295151010909)
                      ·
                        rfl

theorem cell23_7108000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 1, 5, 2].length) (baseStart_7108000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7108000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7108000 prefixEnd_7108000 := by exact prefixLift 7108000
  have htrace : WordTrace (prefixWord ++ tailWord_7108000) baseStart_7108000 baseEnd_7108000 := by
    simpa [prefixWord, tailWord_7108000, baseEnd_7108000] using wordTrace_append hprefix tailTrace_7108000
  have hstable : (prefixWord ++ tailWord_7108000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7108000).length < 2 ^ (prefixWord ++ tailWord_7108000).sum := by decide
  have hdescent : baseEnd_7108000 < baseStart_7108000 := by decide
  rcases family_descends (prefixWord ++ tailWord_7108000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7108047 : List Nat := [1, 1, 2, 1, 1, 4, 4, 2, 3, 2, 2]
def baseStart_7108047 : Nat := 118140960795 + 7108047 * 2 ^ 59
def prefixEnd_7108047 : Nat := 4983230072969 + 3 ^ 40 * 7108047 * 2
def baseEnd_7108047 : Nat := 3649844625749056467123193

theorem tailTrace_7108047 : CollatzResearch.WordTrace tailWord_7108047 prefixEnd_7108047 3649844625749056467123193 := by
  unfold tailWord_7108047
  simp only [CollatzResearch.WordTrace]
  refine ⟨259251772479767151624594395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172834514986511434416396263 259251772479767151624594395)
  ·
    refine ⟨388877658719650727436891593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259251772479767151624594395 388877658719650727436891593)
    ·
      refine ⟨291658244039738045577668695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 388877658719650727436891593 291658244039738045577668695)
      ·
        refine ⟨437487366059607068366503043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291658244039738045577668695 437487366059607068366503043)
        ·
          refine ⟨656231049089410602549754565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 437487366059607068366503043 656231049089410602549754565)
          ·
            refine ⟨123043321704264487978078981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 656231049089410602549754565 123043321704264487978078981)
            ·
              refine ⟨23070622819549591495889809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123043321704264487978078981 23070622819549591495889809)
              ·
                refine ⟨17302967114662193621917357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23070622819549591495889809 17302967114662193621917357)
                ·
                  refine ⟨6488612667998322608219009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17302967114662193621917357 6488612667998322608219009)
                  ·
                    refine ⟨4866459500998741956164257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6488612667998322608219009 4866459500998741956164257)
                    ·
                      refine ⟨3649844625749056467123193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4866459500998741956164257 3649844625749056467123193)
                      ·
                        rfl

theorem cell23_7108047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 2, 3, 2, 2].length) (baseStart_7108047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7108047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7108047 prefixEnd_7108047 := by exact prefixLift 7108047
  have htrace : WordTrace (prefixWord ++ tailWord_7108047) baseStart_7108047 baseEnd_7108047 := by
    simpa [prefixWord, tailWord_7108047, baseEnd_7108047] using wordTrace_append hprefix tailTrace_7108047
  have hstable : (prefixWord ++ tailWord_7108047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7108047).length < 2 ^ (prefixWord ++ tailWord_7108047).sum := by decide
  have hdescent : baseEnd_7108047 < baseStart_7108047 := by decide
  rcases family_descends (prefixWord ++ tailWord_7108047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7108053 : List Nat := [1, 3, 2, 3, 1, 1, 3, 9]
def baseStart_7108053 : Nat := 118140960795 + 7108053 * 2 ^ 59
def prefixEnd_7108053 : Nat := 4983230072969 + 3 ^ 40 * 7108053 * 2
def baseEnd_7108053 : Nat := 135179544690110497912895

theorem tailTrace_7108053 : CollatzResearch.WordTrace tailWord_7108053 prefixEnd_7108053 135179544690110497912895 := by
  unfold tailWord_7108053
  simp only [CollatzResearch.WordTrace]
  refine ⟨259251991317745414649312813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172834660878496943099541875 259251991317745414649312813)
  ·
    refine ⟨97219496744154530493492305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259251991317745414649312813 97219496744154530493492305)
    ·
      refine ⟨72914622558115897870119229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97219496744154530493492305 72914622558115897870119229)
      ·
        refine ⟨27342983459293461701294711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72914622558115897870119229 27342983459293461701294711)
        ·
          refine ⟨41014475188940192551942067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27342983459293461701294711 41014475188940192551942067)
          ·
            refine ⟨61521712783410288827913101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41014475188940192551942067 61521712783410288827913101)
            ·
              refine ⟨23070642293778858310467413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61521712783410288827913101 23070642293778858310467413)
              ·
                refine ⟨135179544690110497912895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23070642293778858310467413 135179544690110497912895)
                ·
                  rfl

theorem cell23_7108053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 9].length) (baseStart_7108053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7108053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7108053 prefixEnd_7108053 := by exact prefixLift 7108053
  have htrace : WordTrace (prefixWord ++ tailWord_7108053) baseStart_7108053 baseEnd_7108053 := by
    simpa [prefixWord, tailWord_7108053, baseEnd_7108053] using wordTrace_append hprefix tailTrace_7108053
  have hstable : (prefixWord ++ tailWord_7108053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7108053).length < 2 ^ (prefixWord ++ tailWord_7108053).sum := by decide
  have hdescent : baseEnd_7108053 < baseStart_7108053 := by decide
  rcases family_descends (prefixWord ++ tailWord_7108053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7108064 : List Nat := [2, 1, 1, 3, 1, 1, 2, 7, 1, 2, 2]
def baseStart_7108064 : Nat := 118140960795 + 7108064 * 2 ^ 59
def prefixEnd_7108064 : Nat := 4983230072969 + 3 ^ 40 * 7108064 * 2
def baseEnd_7108064 : Nat := 3649853354920182900610615

theorem tailTrace_7108064 : CollatzResearch.WordTrace tailWord_7108064 prefixEnd_7108064 3649853354920182900610615 := by
  unfold tailWord_7108064
  simp only [CollatzResearch.WordTrace]
  refine ⟨129626196260352781763981623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172834928347137042351975497 129626196260352781763981623)
  ·
    refine ⟨194439294390529172645972435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129626196260352781763981623 194439294390529172645972435)
    ·
      refine ⟨291658941585793758968958653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194439294390529172645972435 291658941585793758968958653)
      ·
        refine ⟨109372103094672659613359495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 291658941585793758968958653 109372103094672659613359495)
        ·
          refine ⟨164058154642008989420039243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109372103094672659613359495 164058154642008989420039243)
          ·
            refine ⟨246087231963013484130058865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164058154642008989420039243 246087231963013484130058865)
            ·
              refine ⟨184565423972260113097544149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246087231963013484130058865 184565423972260113097544149)
              ·
                refine ⟨4325752124349846400723691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 184565423972260113097544149 4325752124349846400723691)
                ·
                  refine ⟨6488628186524769601085537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4325752124349846400723691 6488628186524769601085537)
                  ·
                    refine ⟨4866471139893577200814153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6488628186524769601085537 4866471139893577200814153)
                    ·
                      refine ⟨3649853354920182900610615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4866471139893577200814153 3649853354920182900610615)
                      ·
                        rfl

theorem cell23_7108064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 7, 1, 2, 2].length) (baseStart_7108064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7108064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7108064 prefixEnd_7108064 := by exact prefixLift 7108064
  have htrace : WordTrace (prefixWord ++ tailWord_7108064) baseStart_7108064 baseEnd_7108064 := by
    simpa [prefixWord, tailWord_7108064, baseEnd_7108064] using wordTrace_append hprefix tailTrace_7108064
  have hstable : (prefixWord ++ tailWord_7108064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7108064).length < 2 ^ (prefixWord ++ tailWord_7108064).sum := by decide
  have hdescent : baseEnd_7108064 < baseStart_7108064 := by decide
  rcases family_descends (prefixWord ++ tailWord_7108064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7108067 : List Nat := [1, 1, 1, 6, 2, 1, 2, 3, 1, 2, 3]
def baseStart_7108067 : Nat := 118140960795 + 7108067 * 2 ^ 59
def prefixEnd_7108067 : Nat := 4983230072969 + 3 ^ 40 * 7108067 * 2
def baseEnd_7108067 : Nat := 3649854895362146388873101

theorem tailTrace_7108067 : CollatzResearch.WordTrace tailWord_7108067 prefixEnd_7108067 3649854895362146388873101 := by
  unfold tailWord_7108067
  simp only [CollatzResearch.WordTrace]
  refine ⟨259252501939694695040322455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172835001293129796693548303 259252501939694695040322455)
  ·
    refine ⟨388878752909542042560483683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259252501939694695040322455 388878752909542042560483683)
    ·
      refine ⟨583318129364313063840725525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388878752909542042560483683 583318129364313063840725525)
      ·
        refine ⟨27343037313952174867534009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 583318129364313063840725525 27343037313952174867534009)
        ·
          refine ⟨20507277985464131150650507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27343037313952174867534009 20507277985464131150650507)
          ·
            refine ⟨30760916978196196725975761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20507277985464131150650507 30760916978196196725975761)
            ·
              refine ⟨23070687733647147544481821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30760916978196196725975761 23070687733647147544481821)
              ·
                refine ⟨8651507900117680329180683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23070687733647147544481821 8651507900117680329180683)
                ·
                  refine ⟨12977261850176520493771025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8651507900117680329180683 12977261850176520493771025)
                  ·
                    refine ⟨9732946387632390370328269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12977261850176520493771025 9732946387632390370328269)
                    ·
                      refine ⟨3649854895362146388873101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9732946387632390370328269 3649854895362146388873101)
                      ·
                        rfl

theorem cell23_7108067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_7108067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7108067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7108067 prefixEnd_7108067 := by exact prefixLift 7108067
  have htrace : WordTrace (prefixWord ++ tailWord_7108067) baseStart_7108067 baseEnd_7108067 := by
    simpa [prefixWord, tailWord_7108067, baseEnd_7108067] using wordTrace_append hprefix tailTrace_7108067
  have hstable : (prefixWord ++ tailWord_7108067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7108067).length < 2 ^ (prefixWord ++ tailWord_7108067).sum := by decide
  have hdescent : baseEnd_7108067 < baseStart_7108067 := by decide
  rcases family_descends (prefixWord ++ tailWord_7108067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7108133 : List Nat := [1, 3, 1, 2, 2, 1, 1, 1, 2, 3, 6]
def baseStart_7108133 : Nat := 118140960795 + 7108133 * 2 ^ 59
def prefixEnd_7108133 : Nat := 4983230072969 + 3 ^ 40 * 7108133 * 2
def baseEnd_7108133 : Nat := 3649888785085343130647797

theorem tailTrace_7108133 : CollatzResearch.WordTrace tailWord_7108133 prefixEnd_7108133 3649888785085343130647797 := by
  unfold tailWord_7108133
  simp only [CollatzResearch.WordTrace]
  refine ⟨259254909157455588312225053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172836606104970392208150035 259254909157455588312225053)
  ·
    refine ⟨97220590934045845617084395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259254909157455588312225053 97220590934045845617084395)
    ·
      refine ⟨145830886401068768425626593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97220590934045845617084395 145830886401068768425626593)
      ·
        refine ⟨109373164800801576319219945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145830886401068768425626593 109373164800801576319219945)
        ·
          refine ⟨82029873600601182239414959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109373164800801576319219945 82029873600601182239414959)
          ·
            refine ⟨123044810400901773359122439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82029873600601182239414959 123044810400901773359122439)
            ·
              refine ⟨184567215601352660038683659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123044810400901773359122439 184567215601352660038683659)
              ·
                refine ⟨276850823402028990058025489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184567215601352660038683659 276850823402028990058025489)
                ·
                  refine ⟨207638117551521742543519117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 276850823402028990058025489 207638117551521742543519117)
                  ·
                    refine ⟨77864294081820653453819669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 207638117551521742543519117 77864294081820653453819669)
                    ·
                      refine ⟨3649888785085343130647797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77864294081820653453819669 3649888785085343130647797)
                      ·
                        rfl

theorem cell23_7108133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_7108133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7108133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7108133 prefixEnd_7108133 := by exact prefixLift 7108133
  have htrace : WordTrace (prefixWord ++ tailWord_7108133) baseStart_7108133 baseEnd_7108133 := by
    simpa [prefixWord, tailWord_7108133, baseEnd_7108133] using wordTrace_append hprefix tailTrace_7108133
  have hstable : (prefixWord ++ tailWord_7108133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7108133).length < 2 ^ (prefixWord ++ tailWord_7108133).sum := by decide
  have hdescent : baseEnd_7108133 < baseStart_7108133 := by decide
  rcases family_descends (prefixWord ++ tailWord_7108133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7108154 : List Nat := [3, 1, 1, 1, 3, 2, 1, 5, 2, 2, 2]
def baseStart_7108154 : Nat := 118140960795 + 7108154 * 2 ^ 59
def prefixEnd_7108154 : Nat := 4983230072969 + 3 ^ 40 * 7108154 * 2
def baseEnd_7108154 : Nat := 3649899568179087548485201

theorem tailTrace_7108154 : CollatzResearch.WordTrace tailWord_7108154 prefixEnd_7108154 3649899568179087548485201 := by
  unfold tailWord_7108154
  simp only [CollatzResearch.WordTrace]
  refine ⟨64813918772594877224684879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172837116726919672599159677 64813918772594877224684879)
  ·
    refine ⟨97220878158892315837027319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64813918772594877224684879 97220878158892315837027319)
    ·
      refine ⟨145831317238338473755540979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97220878158892315837027319 145831317238338473755540979)
      ·
        refine ⟨218746975857507710633311469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145831317238338473755540979 218746975857507710633311469)
        ·
          refine ⟨82030115946565391487491801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218746975857507710633311469 82030115946565391487491801)
          ·
            refine ⟨61522586959924043615618851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82030115946565391487491801 61522586959924043615618851)
            ·
              refine ⟨92283880439886065423428277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61522586959924043615618851 92283880439886065423428277)
              ·
                refine ⟨8651613791239318633446401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92283880439886065423428277 8651613791239318633446401)
                ·
                  refine ⟨6488710343429488975084801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8651613791239318633446401 6488710343429488975084801)
                  ·
                    refine ⟨4866532757572116731313601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6488710343429488975084801 4866532757572116731313601)
                    ·
                      refine ⟨3649899568179087548485201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4866532757572116731313601 3649899568179087548485201)
                      ·
                        rfl

theorem cell23_7108154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 5, 2, 2, 2].length) (baseStart_7108154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7108154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7108154 prefixEnd_7108154 := by exact prefixLift 7108154
  have htrace : WordTrace (prefixWord ++ tailWord_7108154) baseStart_7108154 baseEnd_7108154 := by
    simpa [prefixWord, tailWord_7108154, baseEnd_7108154] using wordTrace_append hprefix tailTrace_7108154
  have hstable : (prefixWord ++ tailWord_7108154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7108154).length < 2 ^ (prefixWord ++ tailWord_7108154).sum := by decide
  have hdescent : baseEnd_7108154 < baseStart_7108154 := by decide
  rcases family_descends (prefixWord ++ tailWord_7108154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7108170 : List Nat := [3, 1, 2, 1, 1, 3, 1, 2, 1, 5, 3]
def baseStart_7108170 : Nat := 118140960795 + 7108170 * 2 ^ 59
def prefixEnd_7108170 : Nat := 4983230072969 + 3 ^ 40 * 7108170 * 2
def baseEnd_7108170 : Nat := 3649907783869559485885127

theorem tailTrace_7108170 : CollatzResearch.WordTrace tailWord_7108170 prefixEnd_7108170 3649907783869559485885127 := by
  unfold tailWord_7108170
  simp only [CollatzResearch.WordTrace]
  refine ⟨64814064664580385907830491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172837505772214362420881309 64814064664580385907830491)
  ·
    refine ⟨97221096996870578861745737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64814064664580385907830491 97221096996870578861745737)
    ·
      refine ⟨72915822747652934146309303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97221096996870578861745737 72915822747652934146309303)
      ·
        refine ⟨109373734121479401219463955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72915822747652934146309303 109373734121479401219463955)
        ·
          refine ⟨164060601182219101829195933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109373734121479401219463955 164060601182219101829195933)
          ·
            refine ⟨61522725443332163185948475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164060601182219101829195933 61522725443332163185948475)
            ·
              refine ⟨92284088164998244778922713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61522725443332163185948475 92284088164998244778922713)
              ·
                refine ⟨69213066123748683584192035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92284088164998244778922713 69213066123748683584192035)
                ·
                  refine ⟨103819599185623025376288053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69213066123748683584192035 103819599185623025376288053)
                  ·
                    refine ⟨9733087423652158629027005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 103819599185623025376288053 9733087423652158629027005)
                    ·
                      refine ⟨3649907783869559485885127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9733087423652158629027005 3649907783869559485885127)
                      ·
                        rfl

theorem cell23_7108170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 1, 5, 3].length) (baseStart_7108170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7108170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7108170 prefixEnd_7108170 := by exact prefixLift 7108170
  have htrace : WordTrace (prefixWord ++ tailWord_7108170) baseStart_7108170 baseEnd_7108170 := by
    simpa [prefixWord, tailWord_7108170, baseEnd_7108170] using wordTrace_append hprefix tailTrace_7108170
  have hstable : (prefixWord ++ tailWord_7108170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7108170).length < 2 ^ (prefixWord ++ tailWord_7108170).sum := by decide
  have hdescent : baseEnd_7108170 < baseStart_7108170 := by decide
  rcases family_descends (prefixWord ++ tailWord_7108170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7108177 : List Nat := [1, 2, 2, 1, 3, 2, 4, 3, 5]
def baseStart_7108177 : Nat := 118140960795 + 7108177 * 2 ^ 59
def prefixEnd_7108177 : Nat := 4983230072969 + 3 ^ 40 * 7108177 * 2
def baseEnd_7108177 : Nat := 405545708692682328721955

theorem tailTrace_7108177 : CollatzResearch.WordTrace tailWord_7108177 prefixEnd_7108177 405545708692682328721955 := by
  unfold tailWord_7108177
  simp only [CollatzResearch.WordTrace]
  refine ⟨259256513969296183826826785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172837675979530789217884523 259256513969296183826826785)
  ·
    refine ⟨194442385476972137870120089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259256513969296183826826785 194442385476972137870120089)
    ·
      refine ⟨145831789107729103402590067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194442385476972137870120089 145831789107729103402590067)
      ·
        refine ⟨218747683661593655103885101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145831789107729103402590067 218747683661593655103885101)
        ·
          refine ⟨82030381373097620663956913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218747683661593655103885101 82030381373097620663956913)
          ·
            refine ⟨61522786029823215497967685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82030381373097620663956913 61522786029823215497967685)
            ·
              refine ⟨11535522380591852905868941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61522786029823215497967685 11535522380591852905868941)
              ·
                refine ⟨4325820892721944839700853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11535522380591852905868941 4325820892721944839700853)
                ·
                  refine ⟨405545708692682328721955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4325820892721944839700853 405545708692682328721955)
                  ·
                    rfl

theorem cell23_7108177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 3, 5].length) (baseStart_7108177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7108177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7108177 prefixEnd_7108177 := by exact prefixLift 7108177
  have htrace : WordTrace (prefixWord ++ tailWord_7108177) baseStart_7108177 baseEnd_7108177 := by
    simpa [prefixWord, tailWord_7108177, baseEnd_7108177] using wordTrace_append hprefix tailTrace_7108177
  have hstable : (prefixWord ++ tailWord_7108177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7108177).length < 2 ^ (prefixWord ++ tailWord_7108177).sum := by decide
  have hdescent : baseEnd_7108177 < baseStart_7108177 := by decide
  rcases family_descends (prefixWord ++ tailWord_7108177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7108182 : List Nat := [5, 2, 2, 2, 2, 1, 1, 2, 2, 1, 3]
def baseStart_7108182 : Nat := 118140960795 + 7108182 * 2 ^ 59
def prefixEnd_7108182 : Nat := 4983230072969 + 3 ^ 40 * 7108182 * 2
def baseEnd_7108182 : Nat := 3649913945637413438935073

theorem tailTrace_7108182 : CollatzResearch.WordTrace tailWord_7108182 prefixEnd_7108182 3649913945637413438935073 := by
  unfold tailWord_7108182
  simp only [CollatzResearch.WordTrace]
  refine ⟨16203543520892379355047425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 172837797556185379787172533 16203543520892379355047425)
  ·
    refine ⟨12152657640669284516285569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16203543520892379355047425 12152657640669284516285569)
    ·
      refine ⟨9114493230501963387214177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12152657640669284516285569 9114493230501963387214177)
      ·
        refine ⟨6835869922876472540410633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9114493230501963387214177 6835869922876472540410633)
        ·
          refine ⟨5126902442157354405307975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6835869922876472540410633 5126902442157354405307975)
          ·
            refine ⟨7690353663236031607961963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5126902442157354405307975 7690353663236031607961963)
            ·
              refine ⟨11535530494854047411942945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7690353663236031607961963 11535530494854047411942945)
              ·
                refine ⟨8651647871140535558957209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11535530494854047411942945 8651647871140535558957209)
                ·
                  refine ⟨6488735903355401669217907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8651647871140535558957209 6488735903355401669217907)
                  ·
                    refine ⟨9733103855033102503826861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6488735903355401669217907 9733103855033102503826861)
                    ·
                      refine ⟨3649913945637413438935073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9733103855033102503826861 3649913945637413438935073)
                      ·
                        rfl

theorem cell23_7108182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_7108182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7108182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7108182 prefixEnd_7108182 := by exact prefixLift 7108182
  have htrace : WordTrace (prefixWord ++ tailWord_7108182) baseStart_7108182 baseEnd_7108182 := by
    simpa [prefixWord, tailWord_7108182, baseEnd_7108182] using wordTrace_append hprefix tailTrace_7108182
  have hstable : (prefixWord ++ tailWord_7108182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7108182).length < 2 ^ (prefixWord ++ tailWord_7108182).sum := by decide
  have hdescent : baseEnd_7108182 < baseStart_7108182 := by decide
  rcases family_descends (prefixWord ++ tailWord_7108182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7108188 : List Nat := [2, 2, 4, 1, 2, 3, 1, 2, 2, 2, 2]
def baseStart_7108188 : Nat := 118140960795 + 7108188 * 2 ^ 59
def prefixEnd_7108188 : Nat := 4983230072969 + 3 ^ 40 * 7108188 * 2
def baseEnd_7108188 : Nat := 3649917026521340415460045

theorem tailTrace_7108188 : CollatzResearch.WordTrace tailWord_7108188 prefixEnd_7108188 3649917026521340415460045 := by
  unfold tailWord_7108188
  simp only [CollatzResearch.WordTrace]
  refine ⟨129628457586128166352738609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172837943448170888470318145 129628457586128166352738609)
  ·
    refine ⟨97221343189596124764553957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129628457586128166352738609 97221343189596124764553957)
    ·
      refine ⟨18229001848049273393353867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97221343189596124764553957 18229001848049273393353867)
      ·
        refine ⟨27343502772073910090030801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18229001848049273393353867 27343502772073910090030801)
        ·
          refine ⟨20507627079055432567523101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27343502772073910090030801 20507627079055432567523101)
          ·
            refine ⟨7690360154645787212821163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20507627079055432567523101 7690360154645787212821163)
            ·
              refine ⟨11535540231968680819231745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7690360154645787212821163 11535540231968680819231745)
              ·
                refine ⟨8651655173976510614423809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11535540231968680819231745 8651655173976510614423809)
                ·
                  refine ⟨6488741380482382960817857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8651655173976510614423809 6488741380482382960817857)
                  ·
                    refine ⟨4866556035361787220613393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6488741380482382960817857 4866556035361787220613393)
                    ·
                      refine ⟨3649917026521340415460045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4866556035361787220613393 3649917026521340415460045)
                      ·
                        rfl

theorem cell23_7108188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 2, 2, 2, 2].length) (baseStart_7108188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7108188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7108188 prefixEnd_7108188 := by exact prefixLift 7108188
  have htrace : WordTrace (prefixWord ++ tailWord_7108188) baseStart_7108188 baseEnd_7108188 := by
    simpa [prefixWord, tailWord_7108188, baseEnd_7108188] using wordTrace_append hprefix tailTrace_7108188
  have hstable : (prefixWord ++ tailWord_7108188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7108188).length < 2 ^ (prefixWord ++ tailWord_7108188).sum := by decide
  have hdescent : baseEnd_7108188 < baseStart_7108188 := by decide
  rcases family_descends (prefixWord ++ tailWord_7108188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7108247 : List Nat := [1, 1, 3, 3, 2, 2, 1, 1, 4, 2, 3]
def baseStart_7108247 : Nat := 118140960795 + 7108247 * 2 ^ 59
def prefixEnd_7108247 : Nat := 4983230072969 + 3 ^ 40 * 7108247 * 2
def baseEnd_7108247 : Nat := 3649947321879955684622273

theorem tailTrace_7108247 : CollatzResearch.WordTrace tailWord_7108247 prefixEnd_7108247 3649947321879955684622273 := by
  unfold tailWord_7108247
  simp only [CollatzResearch.WordTrace]
  refine ⟨259259067079042585781874995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172839378052695057187916663 259259067079042585781874995)
  ·
    refine ⟨388888600618563878672812493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259259067079042585781874995 388888600618563878672812493)
    ·
      refine ⟨145833225231961454502304685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 388888600618563878672812493 145833225231961454502304685)
      ·
        refine ⟨54687459461985545438364257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145833225231961454502304685 54687459461985545438364257)
        ·
          refine ⟨41015594596489159078773193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54687459461985545438364257 41015594596489159078773193)
          ·
            refine ⟨30761695947366869309079895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41015594596489159078773193 30761695947366869309079895)
            ·
              refine ⟨46142543921050303963619843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30761695947366869309079895 46142543921050303963619843)
              ·
                refine ⟨69213815881575455945429765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46142543921050303963619843 69213815881575455945429765)
                ·
                  refine ⟨12977590477795397989768081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69213815881575455945429765 12977590477795397989768081)
                  ·
                    refine ⟨9733192858346548492326061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12977590477795397989768081 9733192858346548492326061)
                    ·
                      refine ⟨3649947321879955684622273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9733192858346548492326061 3649947321879955684622273)
                      ·
                        rfl

theorem cell23_7108247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 4, 2, 3].length) (baseStart_7108247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7108247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7108247 prefixEnd_7108247 := by exact prefixLift 7108247
  have htrace : WordTrace (prefixWord ++ tailWord_7108247) baseStart_7108247 baseEnd_7108247 := by
    simpa [prefixWord, tailWord_7108247, baseEnd_7108247] using wordTrace_append hprefix tailTrace_7108247
  have hstable : (prefixWord ++ tailWord_7108247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7108247).length < 2 ^ (prefixWord ++ tailWord_7108247).sum := by decide
  have hdescent : baseEnd_7108247 < baseStart_7108247 := by decide
  rcases family_descends (prefixWord ++ tailWord_7108247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7108301 : List Nat := [1, 6, 2, 1, 1, 2, 2, 2, 6]
def baseStart_7108301 : Nat := 118140960795 + 7108301 * 2 ^ 59
def prefixEnd_7108301 : Nat := 4983230072969 + 3 ^ 40 * 7108301 * 2
def baseEnd_7108301 : Nat := 405552783315033163705225

theorem tailTrace_7108301 : CollatzResearch.WordTrace tailWord_7108301 prefixEnd_7108301 405552783315033163705225 := by
  unfold tailWord_7108301
  simp only [CollatzResearch.WordTrace]
  refine ⟨259261036620846953004340757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172840691080564635336227171 259261036620846953004340757)
  ·
    refine ⟨12152861091602200922078473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 259261036620846953004340757 12152861091602200922078473)
    ·
      refine ⟨9114645818701650691558855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12152861091602200922078473 9114645818701650691558855)
      ·
        refine ⟨13671968728052476037338283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9114645818701650691558855 13671968728052476037338283)
        ·
          refine ⟨20507953092078714056007425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13671968728052476037338283 20507953092078714056007425)
          ·
            refine ⟨15380964819059035542005569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20507953092078714056007425 15380964819059035542005569)
            ·
              refine ⟨11535723614294276656504177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15380964819059035542005569 11535723614294276656504177)
              ·
                refine ⟨8651792710720707492378133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11535723614294276656504177 8651792710720707492378133)
                ·
                  refine ⟨405552783315033163705225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8651792710720707492378133 405552783315033163705225)
                  ·
                    rfl

theorem cell23_7108301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_7108301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7108301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7108301 prefixEnd_7108301 := by exact prefixLift 7108301
  have htrace : WordTrace (prefixWord ++ tailWord_7108301) baseStart_7108301 baseEnd_7108301 := by
    simpa [prefixWord, tailWord_7108301, baseEnd_7108301] using wordTrace_append hprefix tailTrace_7108301
  have hstable : (prefixWord ++ tailWord_7108301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7108301).length < 2 ^ (prefixWord ++ tailWord_7108301).sum := by decide
  have hdescent : baseEnd_7108301 < baseStart_7108301 := by decide
  rcases family_descends (prefixWord ++ tailWord_7108301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7108311 : List Nat := [1, 1, 3, 2, 1, 3, 3, 4, 1, 1, 3]
def baseStart_7108311 : Nat := 118140960795 + 7108311 * 2 ^ 59
def prefixEnd_7108311 : Nat := 4983230072969 + 3 ^ 40 * 7108311 * 2
def baseEnd_7108311 : Nat := 3649980184641843434221979

theorem tailTrace_7108311 : CollatzResearch.WordTrace tailWord_7108311 prefixEnd_7108311 3649980184641843434221979 := by
  unfold tailWord_7108311
  simp only [CollatzResearch.WordTrace]
  refine ⟨259261401350810724712204787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172840934233873816474803191 259261401350810724712204787)
  ·
    refine ⟨388892102026216087068307181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259261401350810724712204787 388892102026216087068307181)
    ·
      refine ⟨145834538259831032650615193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 388892102026216087068307181 145834538259831032650615193)
      ·
        refine ⟨109375903694873274487961395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145834538259831032650615193 109375903694873274487961395)
        ·
          refine ⟨164063855542309911731942093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109375903694873274487961395 164063855542309911731942093)
          ·
            refine ⟨61523945828366216899478285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164063855542309911731942093 61523945828366216899478285)
            ·
              refine ⟨23071479685637331337304357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61523945828366216899478285 23071479685637331337304357)
              ·
                refine ⟨4325902441056999625744567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23071479685637331337304357 4325902441056999625744567)
                ·
                  refine ⟨6488853661585499438616851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4325902441056999625744567 6488853661585499438616851)
                  ·
                    refine ⟨9733280492378249157925277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6488853661585499438616851 9733280492378249157925277)
                    ·
                      refine ⟨3649980184641843434221979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9733280492378249157925277 3649980184641843434221979)
                      ·
                        rfl

theorem cell23_7108311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 4, 1, 1, 3].length) (baseStart_7108311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7108311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7108311 prefixEnd_7108311 := by exact prefixLift 7108311
  have htrace : WordTrace (prefixWord ++ tailWord_7108311) baseStart_7108311 baseEnd_7108311 := by
    simpa [prefixWord, tailWord_7108311, baseEnd_7108311] using wordTrace_append hprefix tailTrace_7108311
  have hstable : (prefixWord ++ tailWord_7108311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7108311).length < 2 ^ (prefixWord ++ tailWord_7108311).sum := by decide
  have hdescent : baseEnd_7108311 < baseStart_7108311 := by decide
  rcases family_descends (prefixWord ++ tailWord_7108311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7108334 : List Nat := [4, 1, 2, 1, 1, 2, 2, 4, 1, 1, 4]
def baseStart_7108334 : Nat := 118140960795 + 7108334 * 2 ^ 59
def prefixEnd_7108334 : Nat := 4983230072969 + 3 ^ 40 * 7108334 * 2
def baseEnd_7108334 : Nat := 3649991994696896844234373

theorem tailTrace_7108334 : CollatzResearch.WordTrace tailWord_7108334 prefixEnd_7108334 3649991994696896844234373 := by
  unfold tailWord_7108334
  simp only [CollatzResearch.WordTrace]
  refine ⟨32407780028715924955036507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172841493486484933093528037 32407780028715924955036507)
  ·
    refine ⟨48611670043073887432554761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32407780028715924955036507 48611670043073887432554761)
    ·
      refine ⟨36458752532305415574416071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48611670043073887432554761 36458752532305415574416071)
      ·
        refine ⟨54688128798458123361624107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36458752532305415574416071 54688128798458123361624107)
        ·
          refine ⟨82032193197687185042436161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54688128798458123361624107 82032193197687185042436161)
          ·
            refine ⟨61524144898265388781827121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82032193197687185042436161 61524144898265388781827121)
            ·
              refine ⟨46143108673699041586370341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61524144898265388781827121 46143108673699041586370341)
              ·
                refine ⟨8651832876318570297444439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46143108673699041586370341 8651832876318570297444439)
                ·
                  refine ⟨12977749314477855446166659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8651832876318570297444439 12977749314477855446166659)
                  ·
                    refine ⟨19466623971716783169249989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12977749314477855446166659 19466623971716783169249989)
                    ·
                      refine ⟨3649991994696896844234373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19466623971716783169249989 3649991994696896844234373)
                      ·
                        rfl

theorem cell23_7108334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 4, 1, 1, 4].length) (baseStart_7108334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7108334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7108334 prefixEnd_7108334 := by exact prefixLift 7108334
  have htrace : WordTrace (prefixWord ++ tailWord_7108334) baseStart_7108334 baseEnd_7108334 := by
    simpa [prefixWord, tailWord_7108334, baseEnd_7108334] using wordTrace_append hprefix tailTrace_7108334
  have hstable : (prefixWord ++ tailWord_7108334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7108334).length < 2 ^ (prefixWord ++ tailWord_7108334).sum := by decide
  have hdescent : baseEnd_7108334 < baseStart_7108334 := by decide
  rcases family_descends (prefixWord ++ tailWord_7108334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7108354 : List Nat := [3, 4, 1, 1, 1, 1, 2, 3, 1, 1, 5]
def baseStart_7108354 : Nat := 118140960795 + 7108354 * 2 ^ 59
def prefixEnd_7108354 : Nat := 4983230072969 + 3 ^ 40 * 7108354 * 2
def baseEnd_7108354 : Nat := 3650002264309986765984281

theorem tailTrace_7108354 : CollatzResearch.WordTrace tailWord_7108354 prefixEnd_7108354 3650002264309986765984281 := by
  unfold tailWord_7108354
  simp only [CollatzResearch.WordTrace]
  refine ⟨64815742422413735764005029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172841979793103295370680077 64815742422413735764005029)
  ·
    refine ⟨12152951704202575455750943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64815742422413735764005029 12152951704202575455750943)
    ·
      refine ⟨18229427556303863183626415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12152951704202575455750943 18229427556303863183626415)
      ·
        refine ⟨27344141334455794775439623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18229427556303863183626415 27344141334455794775439623)
        ·
          refine ⟨41016212001683692163159435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27344141334455794775439623 41016212001683692163159435)
          ·
            refine ⟨61524318002525538244739153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41016212001683692163159435 61524318002525538244739153)
            ·
              refine ⟨46143238501894153683554365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61524318002525538244739153 46143238501894153683554365)
              ·
                refine ⟨17303714438210307631332887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46143238501894153683554365 17303714438210307631332887)
                ·
                  refine ⟨25955571657315461446999331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17303714438210307631332887 25955571657315461446999331)
                  ·
                    refine ⟨38933357485973192170498997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25955571657315461446999331 38933357485973192170498997)
                    ·
                      refine ⟨3650002264309986765984281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38933357485973192170498997 3650002264309986765984281)
                      ·
                        rfl

theorem cell23_7108354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_7108354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7108354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7108354 prefixEnd_7108354 := by exact prefixLift 7108354
  have htrace : WordTrace (prefixWord ++ tailWord_7108354) baseStart_7108354 baseEnd_7108354 := by
    simpa [prefixWord, tailWord_7108354, baseEnd_7108354] using wordTrace_append hprefix tailTrace_7108354
  have hstable : (prefixWord ++ tailWord_7108354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7108354).length < 2 ^ (prefixWord ++ tailWord_7108354).sum := by decide
  have hdescent : baseEnd_7108354 < baseStart_7108354 := by decide
  rcases family_descends (prefixWord ++ tailWord_7108354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7108464 : List Nat := [2, 1, 1, 1, 4, 1, 1, 7, 5]
def baseStart_7108464 : Nat := 118140960795 + 7108464 * 2 ^ 59
def prefixEnd_7108464 : Nat := 4983230072969 + 3 ^ 40 * 7108464 * 2
def baseEnd_7108464 : Nat := 405562083020220148400975

theorem tailTrace_7108464 : CollatzResearch.WordTrace tailWord_7108464 prefixEnd_7108464 405562083020220148400975 := by
  unfold tailWord_7108464
  simp only [CollatzResearch.WordTrace]
  refine ⟨129633490859628215921262223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172844654479504287895016297 129633490859628215921262223)
  ·
    refine ⟨194450236289442323881893335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129633490859628215921262223 194450236289442323881893335)
    ·
      refine ⟨291675354434163485822840003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194450236289442323881893335 291675354434163485822840003)
      ·
        refine ⟨437513031651245228734260005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291675354434163485822840003 437513031651245228734260005)
        ·
          refine ⟨82033693434608480387673751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 437513031651245228734260005 82033693434608480387673751)
          ·
            refine ⟨123050540151912720581510627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82033693434608480387673751 123050540151912720581510627)
            ·
              refine ⟨184575810227869080872265941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123050540151912720581510627 184575810227869080872265941)
              ·
                refine ⟨4325995552215681582943733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 184575810227869080872265941 4325995552215681582943733)
                ·
                  refine ⟨405562083020220148400975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4325995552215681582943733 405562083020220148400975)
                  ·
                    rfl

theorem cell23_7108464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 7, 5].length) (baseStart_7108464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7108464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7108464 prefixEnd_7108464 := by exact prefixLift 7108464
  have htrace : WordTrace (prefixWord ++ tailWord_7108464) baseStart_7108464 baseEnd_7108464 := by
    simpa [prefixWord, tailWord_7108464, baseEnd_7108464] using wordTrace_append hprefix tailTrace_7108464
  have hstable : (prefixWord ++ tailWord_7108464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7108464).length < 2 ^ (prefixWord ++ tailWord_7108464).sum := by decide
  have hdescent : baseEnd_7108464 < baseStart_7108464 := by decide
  rcases family_descends (prefixWord ++ tailWord_7108464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7108477 : List Nat := [1, 4, 1, 1, 2, 1, 1, 2, 3, 7]
def baseStart_7108477 : Nat := 118140960795 + 7108477 * 2 ^ 59
def prefixEnd_7108477 : Nat := 4983230072969 + 3 ^ 40 * 7108477 * 2
def baseEnd_7108477 : Nat := 1216688474143496594915405

theorem tailTrace_7108477 : CollatzResearch.WordTrace tailWord_7108477 prefixEnd_7108477 1216688474143496594915405 := by
  unfold tailWord_7108477
  simp only [CollatzResearch.WordTrace]
  refine ⟨259267455868209335062747685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172844970578806223375165123 259267455868209335062747685)
  ·
    refine ⟨48612647975289250324265191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 259267455868209335062747685 48612647975289250324265191)
    ·
      refine ⟨72918971962933875486397787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48612647975289250324265191 72918971962933875486397787)
      ·
        refine ⟨109378457944400813229596681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72918971962933875486397787 109378457944400813229596681)
        ·
          refine ⟨82033843458300609922197511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109378457944400813229596681 82033843458300609922197511)
          ·
            refine ⟨123050765187450914883296267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82033843458300609922197511 123050765187450914883296267)
            ·
              refine ⟨184576147781176372324944401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123050765187450914883296267 184576147781176372324944401)
              ·
                refine ⟨138432110835882279243708301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184576147781176372324944401 138432110835882279243708301)
                ·
                  refine ⟨51912041563455854716390613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 138432110835882279243708301 51912041563455854716390613)
                  ·
                    refine ⟨1216688474143496594915405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51912041563455854716390613 1216688474143496594915405)
                    ·
                      rfl

theorem cell23_7108477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 7].length) (baseStart_7108477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7108477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7108477 prefixEnd_7108477 := by exact prefixLift 7108477
  have htrace : WordTrace (prefixWord ++ tailWord_7108477) baseStart_7108477 baseEnd_7108477 := by
    simpa [prefixWord, tailWord_7108477, baseEnd_7108477] using wordTrace_append hprefix tailTrace_7108477
  have hstable : (prefixWord ++ tailWord_7108477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7108477).length < 2 ^ (prefixWord ++ tailWord_7108477).sum := by decide
  have hdescent : baseEnd_7108477 < baseStart_7108477 := by decide
  rcases family_descends (prefixWord ++ tailWord_7108477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7108526 : List Nat := [4, 1, 5, 1, 1, 2, 1, 2, 2, 2, 2]
def baseStart_7108526 : Nat := 118140960795 + 7108526 * 2 ^ 59
def prefixEnd_7108526 : Nat := 4983230072969 + 3 ^ 40 * 7108526 * 2
def baseEnd_7108526 : Nat := 3650090582982560093033491

theorem tailTrace_7108526 : CollatzResearch.WordTrace tailWord_7108526 prefixEnd_7108526 3650090582982560093033491 := by
  unfold tailWord_7108526
  simp only [CollatzResearch.WordTrace]
  refine ⟨32408655380628977053910179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172846162030021210954187621 32408655380628977053910179)
  ·
    refine ⟨48612983070943465580865269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32408655380628977053910179 48612983070943465580865269)
    ·
      refine ⟨4557467162900949898206119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48612983070943465580865269 4557467162900949898206119)
      ·
        refine ⟨6836200744351424847309179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4557467162900949898206119 6836200744351424847309179)
        ·
          refine ⟨10254301116527137270963769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6836200744351424847309179 10254301116527137270963769)
          ·
            refine ⟨7690725837395352953222827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10254301116527137270963769 7690725837395352953222827)
            ·
              refine ⟨11536088756093029429834241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7690725837395352953222827 11536088756093029429834241)
              ·
                refine ⟨8652066567069772072375681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11536088756093029429834241 8652066567069772072375681)
                ·
                  refine ⟨6489049925302329054281761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8652066567069772072375681 6489049925302329054281761)
                  ·
                    refine ⟨4866787443976746790711321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6489049925302329054281761 4866787443976746790711321)
                    ·
                      refine ⟨3650090582982560093033491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4866787443976746790711321 3650090582982560093033491)
                      ·
                        rfl

theorem cell23_7108526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_7108526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7108526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7108526 prefixEnd_7108526 := by exact prefixLift 7108526
  have htrace : WordTrace (prefixWord ++ tailWord_7108526) baseStart_7108526 baseEnd_7108526 := by
    simpa [prefixWord, tailWord_7108526, baseEnd_7108526] using wordTrace_append hprefix tailTrace_7108526
  have hstable : (prefixWord ++ tailWord_7108526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7108526).length < 2 ^ (prefixWord ++ tailWord_7108526).sum := by decide
  have hdescent : baseEnd_7108526 < baseStart_7108526 := by decide
  rcases family_descends (prefixWord ++ tailWord_7108526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7108527 : List Nat := [1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 6]
def baseStart_7108527 : Nat := 118140960795 + 7108527 * 2 ^ 59
def prefixEnd_7108527 : Nat := 4983230072969 + 3 ^ 40 * 7108527 * 2
def baseEnd_7108527 : Nat := 3650091096463214589120985

theorem tailTrace_7108527 : CollatzResearch.WordTrace tailWord_7108527 prefixEnd_7108527 3650091096463214589120985 := by
  unfold tailWord_7108527
  simp only [CollatzResearch.WordTrace]
  refine ⟨259269279518028193602067835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172846186345352129068045223 259269279518028193602067835)
  ·
    refine ⟨388903919277042290403101753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259269279518028193602067835 388903919277042290403101753)
    ·
      refine ⟨291677939457781717802326315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 388903919277042290403101753 291677939457781717802326315)
      ·
        refine ⟨437516909186672576703489473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291677939457781717802326315 437516909186672576703489473)
        ·
          refine ⟨328137681890004432527617105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 437516909186672576703489473 328137681890004432527617105)
          ·
            refine ⟨246103261417503324395712829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 328137681890004432527617105 246103261417503324395712829)
            ·
              refine ⟨92288723031563746648392311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 246103261417503324395712829 92288723031563746648392311)
              ·
                refine ⟨138433084547345619972588467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92288723031563746648392311 138433084547345619972588467)
                ·
                  refine ⟨207649626821018429958882701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138433084547345619972588467 207649626821018429958882701)
                  ·
                    refine ⟨77868610057881911234581013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 207649626821018429958882701 77868610057881911234581013)
                    ·
                      refine ⟨3650091096463214589120985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77868610057881911234581013 3650091096463214589120985)
                      ·
                        rfl

theorem cell23_7108527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 6].length) (baseStart_7108527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7108527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7108527 prefixEnd_7108527 := by exact prefixLift 7108527
  have htrace : WordTrace (prefixWord ++ tailWord_7108527) baseStart_7108527 baseEnd_7108527 := by
    simpa [prefixWord, tailWord_7108527, baseEnd_7108527] using wordTrace_append hprefix tailTrace_7108527
  have hstable : (prefixWord ++ tailWord_7108527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7108527).length < 2 ^ (prefixWord ++ tailWord_7108527).sum := by decide
  have hdescent : baseEnd_7108527 < baseStart_7108527 := by decide
  rcases family_descends (prefixWord ++ tailWord_7108527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7108541 : List Nat := [1, 4, 1, 2, 3, 1, 1, 3, 3, 4]
def baseStart_7108541 : Nat := 118140960795 + 7108541 * 2 ^ 59
def prefixEnd_7108541 : Nat := 4983230072969 + 3 ^ 40 * 7108541 * 2
def baseEnd_7108541 : Nat := 1216699428397459178115307

theorem tailTrace_7108541 : CollatzResearch.WordTrace tailWord_7108541 prefixEnd_7108541 1216699428397459178115307 := by
  unfold tailWord_7108541
  simp only [CollatzResearch.WordTrace]
  refine ⟨259269790139977473993077477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172846526759984982662051651 259269790139977473993077477)
  ·
    refine ⟨48613085651245776373702027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 259269790139977473993077477 48613085651245776373702027)
    ·
      refine ⟨72919628476868664560553041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48613085651245776373702027 72919628476868664560553041)
      ·
        refine ⟨54689721357651498420414781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72919628476868664560553041 54689721357651498420414781)
        ·
          refine ⟨20508645509119311907655543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54689721357651498420414781 20508645509119311907655543)
          ·
            refine ⟨30762968263678967861483315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20508645509119311907655543 30762968263678967861483315)
            ·
              refine ⟨46144452395518451792224973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30762968263678967861483315 46144452395518451792224973)
              ·
                refine ⟨17304169648319419422084365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46144452395518451792224973 17304169648319419422084365)
                ·
                  refine ⟨6489063618119782283281637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17304169648319419422084365 6489063618119782283281637)
                  ·
                    refine ⟨1216699428397459178115307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6489063618119782283281637 1216699428397459178115307)
                    ·
                      rfl

theorem cell23_7108541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 3, 3, 4].length) (baseStart_7108541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7108541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7108541 prefixEnd_7108541 := by exact prefixLift 7108541
  have htrace : WordTrace (prefixWord ++ tailWord_7108541) baseStart_7108541 baseEnd_7108541 := by
    simpa [prefixWord, tailWord_7108541, baseEnd_7108541] using wordTrace_append hprefix tailTrace_7108541
  have hstable : (prefixWord ++ tailWord_7108541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7108541).length < 2 ^ (prefixWord ++ tailWord_7108541).sum := by decide
  have hdescent : baseEnd_7108541 < baseStart_7108541 := by decide
  rcases family_descends (prefixWord ++ tailWord_7108541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7108554 : List Nat := [3, 1, 2, 1, 2, 1, 2, 5, 6]
def baseStart_7108554 : Nat := 118140960795 + 7108554 * 2 ^ 59
def prefixEnd_7108554 : Nat := 4983230072969 + 3 ^ 40 * 7108554 * 2
def baseEnd_7108554 : Nat := 405567217826765109275929

theorem tailTrace_7108554 : CollatzResearch.WordTrace tailWord_7108554 prefixEnd_7108554 405567217826765109275929 := by
  unfold tailWord_7108554
  simp only [CollatzResearch.WordTrace]
  refine ⟨64817566072232594303325179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172846842859286918142200477 64817566072232594303325179)
  ·
    refine ⟨97226349108348891454987769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64817566072232594303325179 97226349108348891454987769)
    ·
      refine ⟨72919761831261668591240827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97226349108348891454987769 72919761831261668591240827)
      ·
        refine ⟨109379642746892502886861241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72919761831261668591240827 109379642746892502886861241)
        ·
          refine ⟨82034732060169377165145931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109379642746892502886861241 82034732060169377165145931)
          ·
            refine ⟨123052098090254065747718897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82034732060169377165145931 123052098090254065747718897)
            ·
              refine ⟨92289073567690549310789173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123052098090254065747718897 92289073567690549310789173)
              ·
                refine ⟨8652100646970988997886485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92289073567690549310789173 8652100646970988997886485)
                ·
                  refine ⟨405567217826765109275929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8652100646970988997886485 405567217826765109275929)
                  ·
                    rfl

theorem cell23_7108554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 5, 6].length) (baseStart_7108554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7108554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7108554 prefixEnd_7108554 := by exact prefixLift 7108554
  have htrace : WordTrace (prefixWord ++ tailWord_7108554) baseStart_7108554 baseEnd_7108554 := by
    simpa [prefixWord, tailWord_7108554, baseEnd_7108554] using wordTrace_append hprefix tailTrace_7108554
  have hstable : (prefixWord ++ tailWord_7108554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7108554).length < 2 ^ (prefixWord ++ tailWord_7108554).sum := by decide
  have hdescent : baseEnd_7108554 < baseStart_7108554 := by decide
  rcases family_descends (prefixWord ++ tailWord_7108554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7108575 : List Nat := [1, 1, 2, 3, 4, 3, 1, 3, 1, 4]
def baseStart_7108575 : Nat := 118140960795 + 7108575 * 2 ^ 59
def prefixEnd_7108575 : Nat := 4983230072969 + 3 ^ 40 * 7108575 * 2
def baseEnd_7108575 : Nat := 1216705247844876800440255

theorem tailTrace_7108575 : CollatzResearch.WordTrace tailWord_7108575 prefixEnd_7108575 1216705247844876800440255 := by
  unfold tailWord_7108575
  simp only [CollatzResearch.WordTrace]
  refine ⟨259271030221854297799815179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172847353481236198533210119 259271030221854297799815179)
  ·
    refine ⟨388906545332781446699722769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259271030221854297799815179 388906545332781446699722769)
    ·
      refine ⟨291679908999586085024792077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 388906545332781446699722769 291679908999586085024792077)
      ·
        refine ⟨109379965874844781884297029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 291679908999586085024792077 109379965874844781884297029)
        ·
          refine ⟨20508743601533396603305693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109379965874844781884297029 20508743601533396603305693)
          ·
            refine ⟨7690778850575023726239635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20508743601533396603305693 7690778850575023726239635)
            ·
              refine ⟨11536168275862535589359453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7690778850575023726239635 11536168275862535589359453)
              ·
                refine ⟨4326063103448450846009795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11536168275862535589359453 4326063103448450846009795)
                ·
                  refine ⟨6489094655172676269014693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4326063103448450846009795 6489094655172676269014693)
                  ·
                    refine ⟨1216705247844876800440255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6489094655172676269014693 1216705247844876800440255)
                    ·
                      rfl

theorem cell23_7108575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 3, 1, 4].length) (baseStart_7108575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7108575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7108575 prefixEnd_7108575 := by exact prefixLift 7108575
  have htrace : WordTrace (prefixWord ++ tailWord_7108575) baseStart_7108575 baseEnd_7108575 := by
    simpa [prefixWord, tailWord_7108575, baseEnd_7108575] using wordTrace_append hprefix tailTrace_7108575
  have hstable : (prefixWord ++ tailWord_7108575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7108575).length < 2 ^ (prefixWord ++ tailWord_7108575).sum := by decide
  have hdescent : baseEnd_7108575 < baseStart_7108575 := by decide
  rcases family_descends (prefixWord ++ tailWord_7108575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7108584 : List Nat := [2, 1, 4, 1, 1, 1, 1, 2, 5, 5]
def baseStart_7108584 : Nat := 118140960795 + 7108584 * 2 ^ 59
def prefixEnd_7108584 : Nat := 4983230072969 + 3 ^ 40 * 7108584 * 2
def baseEnd_7108584 : Nat := 1216706788286840288702741

theorem tailTrace_7108584 : CollatzResearch.WordTrace tailWord_7108584 prefixEnd_7108584 1216706788286840288702741 := by
  unfold tailWord_7108584
  simp only [CollatzResearch.WordTrace]
  refine ⟨129635679239410846168446403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172847572319214461557928537 129635679239410846168446403)
  ·
    refine ⟨194453518859116269252669605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129635679239410846168446403 194453518859116269252669605)
    ·
      refine ⟨36460034786084300484875551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 194453518859116269252669605 36460034786084300484875551)
      ·
        refine ⟨54690052179126450727313327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36460034786084300484875551 54690052179126450727313327)
        ·
          refine ⟨82035078268689676090969991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54690052179126450727313327 82035078268689676090969991)
          ·
            refine ⟨123052617403034514136454987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82035078268689676090969991 123052617403034514136454987)
            ·
              refine ⟨184578926104551771204682481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123052617403034514136454987 184578926104551771204682481)
              ·
                refine ⟨138434194578413828403511861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184578926104551771204682481 138434194578413828403511861)
                ·
                  refine ⟨12978205741726296412829237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 138434194578413828403511861 12978205741726296412829237)
                  ·
                    refine ⟨1216706788286840288702741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12978205741726296412829237 1216706788286840288702741)
                    ·
                      rfl

theorem cell23_7108584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_7108584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7108584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7108584 prefixEnd_7108584 := by exact prefixLift 7108584
  have htrace : WordTrace (prefixWord ++ tailWord_7108584) baseStart_7108584 baseEnd_7108584 := by
    simpa [prefixWord, tailWord_7108584, baseEnd_7108584] using wordTrace_append hprefix tailTrace_7108584
  have hstable : (prefixWord ++ tailWord_7108584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7108584).length < 2 ^ (prefixWord ++ tailWord_7108584).sum := by decide
  have hdescent : baseEnd_7108584 < baseStart_7108584 := by decide
  rcases family_descends (prefixWord ++ tailWord_7108584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7108624 : List Nat := [2, 1, 1, 1, 1, 1, 1, 4, 2, 6, 3]
def baseStart_7108624 : Nat := 118140960795 + 7108624 * 2 ^ 59
def prefixEnd_7108624 : Nat := 4983230072969 + 3 ^ 40 * 7108624 * 2
def baseEnd_7108624 : Nat := 3650140904086700709608039

theorem tailTrace_7108624 : CollatzResearch.WordTrace tailWord_7108624 prefixEnd_7108624 3650140904086700709608039 := by
  unfold tailWord_7108624
  simp only [CollatzResearch.WordTrace]
  refine ⟨129636408699338389584174463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172848544932451186112232617 129636408699338389584174463)
  ·
    refine ⟨194454613049007584376261695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129636408699338389584174463 194454613049007584376261695)
    ·
      refine ⟨291681919573511376564392543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194454613049007584376261695 291681919573511376564392543)
      ·
        refine ⟨437522879360267064846588815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291681919573511376564392543 437522879360267064846588815)
        ·
          refine ⟨656284319040400597269883223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 437522879360267064846588815 656284319040400597269883223)
          ·
            refine ⟨984426478560600895904824835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 656284319040400597269883223 984426478560600895904824835)
            ·
              refine ⟨1476639717840901343857237253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 984426478560600895904824835 1476639717840901343857237253)
              ·
                refine ⟨276869947095169001973231985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1476639717840901343857237253 276869947095169001973231985)
                ·
                  refine ⟨207652460321376751479923989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 276869947095169001973231985 207652460321376751479923989)
                  ·
                    refine ⟨9733709077564535225621437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 207652460321376751479923989 9733709077564535225621437)
                    ·
                      refine ⟨3650140904086700709608039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9733709077564535225621437 3650140904086700709608039)
                      ·
                        rfl

theorem cell23_7108624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 2, 6, 3].length) (baseStart_7108624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7108624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7108624 prefixEnd_7108624 := by exact prefixLift 7108624
  have htrace : WordTrace (prefixWord ++ tailWord_7108624) baseStart_7108624 baseEnd_7108624 := by
    simpa [prefixWord, tailWord_7108624, baseEnd_7108624] using wordTrace_append hprefix tailTrace_7108624
  have hstable : (prefixWord ++ tailWord_7108624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7108624).length < 2 ^ (prefixWord ++ tailWord_7108624).sum := by decide
  have hdescent : baseEnd_7108624 < baseStart_7108624 := by decide
  rcases family_descends (prefixWord ++ tailWord_7108624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7108644 : List Nat := [2, 3, 1, 4, 13]
def baseStart_7108644 : Nat := 118140960795 + 7108644 * 2 ^ 59
def prefixEnd_7108644 : Nat := 4983230072969 + 3 ^ 40 * 7108644 * 2
def baseEnd_7108644 : Nat := 5007066081892716915443

theorem tailTrace_7108644 : CollatzResearch.WordTrace tailWord_7108644 prefixEnd_7108644 5007066081892716915443 := by
  unfold tailWord_7108644
  simp only [CollatzResearch.WordTrace]
  refine ⟨129636773429302161292038493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172849031239069548389384657 129636773429302161292038493)
  ·
    refine ⟨48613790035988310484514435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 129636773429302161292038493 48613790035988310484514435)
    ·
      refine ⟨72920685053982465726771653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48613790035988310484514435 72920685053982465726771653)
      ·
        refine ⟨13672628447621712323769685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72920685053982465726771653 13672628447621712323769685)
        ·
          refine ⟨5007066081892716915443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 13672628447621712323769685 5007066081892716915443)
          ·
            rfl

theorem cell23_7108644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 13].length) (baseStart_7108644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7108644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7108644 prefixEnd_7108644 := by exact prefixLift 7108644
  have htrace : WordTrace (prefixWord ++ tailWord_7108644) baseStart_7108644 baseEnd_7108644 := by
    simpa [prefixWord, tailWord_7108644, baseEnd_7108644] using wordTrace_append hprefix tailTrace_7108644
  have hstable : (prefixWord ++ tailWord_7108644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7108644).length < 2 ^ (prefixWord ++ tailWord_7108644).sum := by decide
  have hdescent : baseEnd_7108644 < baseStart_7108644 := by decide
  rcases family_descends (prefixWord ++ tailWord_7108644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7108671 : List Nat := [1, 1, 2, 2, 3, 1, 3, 3, 1, 3, 3]
def baseStart_7108671 : Nat := 118140960795 + 7108671 * 2 ^ 59
def prefixEnd_7108671 : Nat := 4983230072969 + 3 ^ 40 * 7108671 * 2
def baseEnd_7108671 : Nat := 3650165037677462025720323

theorem tailTrace_7108671 : CollatzResearch.WordTrace tailWord_7108671 prefixEnd_7108671 3650165037677462025720323 := by
  unfold tailWord_7108671
  simp only [CollatzResearch.WordTrace]
  refine ⟨259274531629506506195309867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172849687753004337463539911 259274531629506506195309867)
  ·
    refine ⟨388911797444259759292964801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259274531629506506195309867 388911797444259759292964801)
    ·
      refine ⟨291683848083194819469723601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 388911797444259759292964801 291683848083194819469723601)
      ·
        refine ⟨218762886062396114602292701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291683848083194819469723601 218762886062396114602292701)
        ·
          refine ⟨82036082273398542975859763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 218762886062396114602292701 82036082273398542975859763)
          ·
            refine ⟨123054123410097814463789645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82036082273398542975859763 123054123410097814463789645)
            ·
              refine ⟨46145296278786680423921117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123054123410097814463789645 46145296278786680423921117)
              ·
                refine ⟨17304486104545005158970419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46145296278786680423921117 17304486104545005158970419)
                ·
                  refine ⟨25956729156817507738455629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17304486104545005158970419 25956729156817507738455629)
                  ·
                    refine ⟨9733773433806565401920861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25956729156817507738455629 9733773433806565401920861)
                    ·
                      refine ⟨3650165037677462025720323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9733773433806565401920861 3650165037677462025720323)
                      ·
                        rfl

theorem cell23_7108671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 3, 1, 3, 3].length) (baseStart_7108671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7108671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7108671 prefixEnd_7108671 := by exact prefixLift 7108671
  have htrace : WordTrace (prefixWord ++ tailWord_7108671) baseStart_7108671 baseEnd_7108671 := by
    simpa [prefixWord, tailWord_7108671, baseEnd_7108671] using wordTrace_append hprefix tailTrace_7108671
  have hstable : (prefixWord ++ tailWord_7108671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7108671).length < 2 ^ (prefixWord ++ tailWord_7108671).sum := by decide
  have hdescent : baseEnd_7108671 < baseStart_7108671 := by decide
  rcases family_descends (prefixWord ++ tailWord_7108671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7108722 : List Nat := [3, 2, 1, 2, 2, 3, 3, 1, 2, 1, 3]
def baseStart_7108722 : Nat := 118140960795 + 7108722 * 2 ^ 59
def prefixEnd_7108722 : Nat := 4983230072969 + 3 ^ 40 * 7108722 * 2
def baseEnd_7108722 : Nat := 3650191225190841326182589

theorem tailTrace_7108722 : CollatzResearch.WordTrace tailWord_7108722 prefixEnd_7108722 3650191225190841326182589 := by
  unfold tailWord_7108722
  simp only [CollatzResearch.WordTrace]
  refine ⟨64819097938080435476354105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172850927834881161270277613 64819097938080435476354105)
  ·
    refine ⟨48614323453560326607265579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64819097938080435476354105 48614323453560326607265579)
    ·
      refine ⟨72921485180340489910898369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48614323453560326607265579 72921485180340489910898369)
      ·
        refine ⟨54691113885255367433173777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72921485180340489910898369 54691113885255367433173777)
        ·
          refine ⟨41018335413941525574880333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54691113885255367433173777 41018335413941525574880333)
          ·
            refine ⟨15381875780228072090580125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41018335413941525574880333 15381875780228072090580125)
            ·
              refine ⟨5768203417585527033967547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15381875780228072090580125 5768203417585527033967547)
              ·
                refine ⟨8652305126378290550951321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5768203417585527033967547 8652305126378290550951321)
                ·
                  refine ⟨6489228844783717913213491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8652305126378290550951321 6489228844783717913213491)
                  ·
                    refine ⟨9733843267175576869820237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6489228844783717913213491 9733843267175576869820237)
                    ·
                      refine ⟨3650191225190841326182589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9733843267175576869820237 3650191225190841326182589)
                      ·
                        rfl

theorem cell23_7108722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 3, 1, 2, 1, 3].length) (baseStart_7108722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7108722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7108722 prefixEnd_7108722 := by exact prefixLift 7108722
  have htrace : WordTrace (prefixWord ++ tailWord_7108722) baseStart_7108722 baseEnd_7108722 := by
    simpa [prefixWord, tailWord_7108722, baseEnd_7108722] using wordTrace_append hprefix tailTrace_7108722
  have hstable : (prefixWord ++ tailWord_7108722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7108722).length < 2 ^ (prefixWord ++ tailWord_7108722).sum := by decide
  have hdescent : baseEnd_7108722 < baseStart_7108722 := by decide
  rcases family_descends (prefixWord ++ tailWord_7108722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7108761 : List Nat := [1, 2, 1, 2, 1, 2, 1, 3, 4, 3, 3]
def baseStart_7108761 : Nat := 118140960795 + 7108761 * 2 ^ 59
def prefixEnd_7108761 : Nat := 4983230072969 + 3 ^ 40 * 7108761 * 2
def baseEnd_7108761 : Nat := 3650211250936366673594909

theorem tailTrace_7108761 : CollatzResearch.WordTrace tailWord_7108761 prefixEnd_7108761 3650211250936366673594909 := by
  unfold tailWord_7108761
  simp only [CollatzResearch.WordTrace]
  refine ⟨259277814199180451566086137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172851876132786967710724091 259277814199180451566086137)
  ·
    refine ⟨194458360649385338674564603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259277814199180451566086137 194458360649385338674564603)
    ·
      refine ⟨291687540974078008011846905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194458360649385338674564603 291687540974078008011846905)
      ·
        refine ⟨218765655730558506008885179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291687540974078008011846905 218765655730558506008885179)
        ·
          refine ⟨328148483595837759013327769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218765655730558506008885179 328148483595837759013327769)
          ·
            refine ⟨246111362696878319259995827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 328148483595837759013327769 246111362696878319259995827)
            ·
              refine ⟨369167044045317478889993741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246111362696878319259995827 369167044045317478889993741)
              ·
                refine ⟨138437641516994054583747653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 369167044045317478889993741 138437641516994054583747653)
                ·
                  refine ⟨25957057784436385234452685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 138437641516994054583747653 25957057784436385234452685)
                  ·
                    refine ⟨9733896669163644462919757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25957057784436385234452685 9733896669163644462919757)
                    ·
                      refine ⟨3650211250936366673594909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9733896669163644462919757 3650211250936366673594909)
                      ·
                        rfl

theorem cell23_7108761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 4, 3, 3].length) (baseStart_7108761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7108761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7108761 prefixEnd_7108761 := by exact prefixLift 7108761
  have htrace : WordTrace (prefixWord ++ tailWord_7108761) baseStart_7108761 baseEnd_7108761 := by
    simpa [prefixWord, tailWord_7108761, baseEnd_7108761] using wordTrace_append hprefix tailTrace_7108761
  have hstable : (prefixWord ++ tailWord_7108761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7108761).length < 2 ^ (prefixWord ++ tailWord_7108761).sum := by decide
  have hdescent : baseEnd_7108761 < baseStart_7108761 := by decide
  rcases family_descends (prefixWord ++ tailWord_7108761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7108768 : List Nat := [2, 1, 1, 4, 2, 4, 1, 1, 7]
def baseStart_7108768 : Nat := 118140960795 + 7108768 * 2 ^ 59
def prefixEnd_7108768 : Nat := 4983230072969 + 3 ^ 40 * 7108768 * 2
def baseEnd_7108768 : Nat := 405579427255660905134153

theorem tailTrace_7108768 : CollatzResearch.WordTrace tailWord_7108768 prefixEnd_7108768 405579427255660905134153 := by
  unfold tailWord_7108768
  simp only [CollatzResearch.WordTrace]
  refine ⟨129639034755077545880795479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172852046340103394507727305 129639034755077545880795479)
  ·
    refine ⟨194458552132616318821193219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129639034755077545880795479 194458552132616318821193219)
    ·
      refine ⟨291687828198924478231789829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194458552132616318821193219 291687828198924478231789829)
      ·
        refine ⟨54691467787298339668460593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 291687828198924478231789829 54691467787298339668460593)
        ·
          refine ⟨41018600840473754751345445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54691467787298339668460593 41018600840473754751345445)
          ·
            refine ⟨7690987657588829015877271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41018600840473754751345445 7690987657588829015877271)
            ·
              refine ⟨11536481486383243523815907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7690987657588829015877271 11536481486383243523815907)
              ·
                refine ⟨17304722229574865285723861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11536481486383243523815907 17304722229574865285723861)
                ·
                  refine ⟨405579427255660905134153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17304722229574865285723861 405579427255660905134153)
                  ·
                    rfl

theorem cell23_7108768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 1, 7].length) (baseStart_7108768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7108768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7108768 prefixEnd_7108768 := by exact prefixLift 7108768
  have htrace : WordTrace (prefixWord ++ tailWord_7108768) baseStart_7108768 baseEnd_7108768 := by
    simpa [prefixWord, tailWord_7108768, baseEnd_7108768] using wordTrace_append hprefix tailTrace_7108768
  have hstable : (prefixWord ++ tailWord_7108768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7108768).length < 2 ^ (prefixWord ++ tailWord_7108768).sum := by decide
  have hdescent : baseEnd_7108768 < baseStart_7108768 := by decide
  rcases family_descends (prefixWord ++ tailWord_7108768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7108822 : List Nat := [5, 2, 1, 2, 1, 1, 1, 1, 2, 5, 2]
def baseStart_7108822 : Nat := 118140960795 + 7108822 * 2 ^ 59
def prefixEnd_7108822 : Nat := 4983230072969 + 3 ^ 40 * 7108822 * 2
def baseEnd_7108822 : Nat := 3650242573256290934932129

theorem tailTrace_7108822 : CollatzResearch.WordTrace tailWord_7108822 prefixEnd_7108822 3650242573256290934932129 := by
  unfold tailWord_7108822
  simp only [CollatzResearch.WordTrace]
  refine ⟨16205002440747466186503545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 172853359367972972656037813 16205002440747466186503545)
  ·
    refine ⟨12153751830560599639877659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16205002440747466186503545 12153751830560599639877659)
    ·
      refine ⟨18230627745840899459816489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12153751830560599639877659 18230627745840899459816489)
      ·
        refine ⟨13672970809380674594862367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18230627745840899459816489 13672970809380674594862367)
        ·
          refine ⟨20509456214071011892293551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13672970809380674594862367 20509456214071011892293551)
          ·
            refine ⟨30764184321106517838440327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20509456214071011892293551 30764184321106517838440327)
            ·
              refine ⟨46146276481659776757660491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30764184321106517838440327 46146276481659776757660491)
              ·
                refine ⟨69219414722489665136490737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46146276481659776757660491 69219414722489665136490737)
                ·
                  refine ⟨51914561041867248852368053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69219414722489665136490737 51914561041867248852368053)
                  ·
                    refine ⟨4866990097675054579909505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51914561041867248852368053 4866990097675054579909505)
                    ·
                      refine ⟨3650242573256290934932129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4866990097675054579909505 3650242573256290934932129)
                      ·
                        rfl

theorem cell23_7108822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_7108822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7108822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7108822 prefixEnd_7108822 := by exact prefixLift 7108822
  have htrace : WordTrace (prefixWord ++ tailWord_7108822) baseStart_7108822 baseEnd_7108822 := by
    simpa [prefixWord, tailWord_7108822, baseEnd_7108822] using wordTrace_append hprefix tailTrace_7108822
  have hstable : (prefixWord ++ tailWord_7108822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7108822).length < 2 ^ (prefixWord ++ tailWord_7108822).sum := by decide
  have hdescent : baseEnd_7108822 < baseStart_7108822 := by decide
  rcases family_descends (prefixWord ++ tailWord_7108822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7108831 : List Nat := [1, 1, 2, 3, 2, 1, 1, 2, 2, 4, 4]
def baseStart_7108831 : Nat := 118140960795 + 7108831 * 2 ^ 59
def prefixEnd_7108831 : Nat := 4983230072969 + 3 ^ 40 * 7108831 * 2
def baseEnd_7108831 : Nat := 3650247194582181399719587

theorem tailTrace_7108831 : CollatzResearch.WordTrace tailWord_7108831 prefixEnd_7108831 3650247194582181399719587 := by
  unfold tailWord_7108831
  simp only [CollatzResearch.WordTrace]
  refine ⟨259280367308926853521134347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172853578205951235680756231 259280367308926853521134347)
  ·
    refine ⟨388920550963390280281701521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259280367308926853521134347 388920550963390280281701521)
    ·
      refine ⟨291690413222542710211276141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 388920550963390280281701521 291690413222542710211276141)
      ·
        refine ⟨109383904958453516329228553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 291690413222542710211276141 109383904958453516329228553)
        ·
          refine ⟨82037928718840137246921415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109383904958453516329228553 82037928718840137246921415)
          ·
            refine ⟨123056893078260205870382123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82037928718840137246921415 123056893078260205870382123)
            ·
              refine ⟨184585339617390308805573185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123056893078260205870382123 184585339617390308805573185)
              ·
                refine ⟨138439004713042731604179889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184585339617390308805573185 138439004713042731604179889)
                ·
                  refine ⟨103829253534782048703134917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 138439004713042731604179889 103829253534782048703134917)
                  ·
                    refine ⟨19467985037771634131837797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 103829253534782048703134917 19467985037771634131837797)
                    ·
                      refine ⟨3650247194582181399719587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19467985037771634131837797 3650247194582181399719587)
                      ·
                        rfl

theorem cell23_7108831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 4, 4].length) (baseStart_7108831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7108831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7108831 prefixEnd_7108831 := by exact prefixLift 7108831
  have htrace : WordTrace (prefixWord ++ tailWord_7108831) baseStart_7108831 baseEnd_7108831 := by
    simpa [prefixWord, tailWord_7108831, baseEnd_7108831] using wordTrace_append hprefix tailTrace_7108831
  have hstable : (prefixWord ++ tailWord_7108831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7108831).length < 2 ^ (prefixWord ++ tailWord_7108831).sum := by decide
  have hdescent : baseEnd_7108831 < baseStart_7108831 := by decide
  rcases family_descends (prefixWord ++ tailWord_7108831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7108861 : List Nat := [1, 4, 1, 1, 1, 1, 1, 2, 3, 2, 6]
def baseStart_7108861 : Nat := 118140960795 + 7108861 * 2 ^ 59
def prefixEnd_7108861 : Nat := 4983230072969 + 3 ^ 40 * 7108861 * 2
def baseEnd_7108861 : Nat := 3650262599001816282344449

theorem tailTrace_7108861 : CollatzResearch.WordTrace tailWord_7108861 prefixEnd_7108861 3650262599001816282344449 := by
  unfold tailWord_7108861
  simp only [CollatzResearch.WordTrace]
  refine ⟨259281461498818168644726437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172854307665878779096484291 259281461498818168644726437)
  ·
    refine ⟨48615274031028406620886207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 259281461498818168644726437 48615274031028406620886207)
    ·
      refine ⟨72922911046542609931329311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48615274031028406620886207 72922911046542609931329311)
      ·
        refine ⟨109384366569813914896993967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72922911046542609931329311 109384366569813914896993967)
        ·
          refine ⟨164076549854720872345490951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109384366569813914896993967 164076549854720872345490951)
          ·
            refine ⟨246114824782081308518236427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164076549854720872345490951 246114824782081308518236427)
            ·
              refine ⟨369172237173121962777354641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246114824782081308518236427 369172237173121962777354641)
              ·
                refine ⟨276879177879841472083015981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 369172237173121962777354641 276879177879841472083015981)
                ·
                  refine ⟨103829691704940552031130993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 276879177879841472083015981 103829691704940552031130993)
                  ·
                    refine ⟨77872268778705414023348245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 103829691704940552031130993 77872268778705414023348245)
                    ·
                      refine ⟨3650262599001816282344449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 77872268778705414023348245 3650262599001816282344449)
                      ·
                        rfl

theorem cell23_7108861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_7108861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7108861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7108861 prefixEnd_7108861 := by exact prefixLift 7108861
  have htrace : WordTrace (prefixWord ++ tailWord_7108861) baseStart_7108861 baseEnd_7108861 := by
    simpa [prefixWord, tailWord_7108861, baseEnd_7108861] using wordTrace_append hprefix tailTrace_7108861
  have hstable : (prefixWord ++ tailWord_7108861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7108861).length < 2 ^ (prefixWord ++ tailWord_7108861).sum := by decide
  have hdescent : baseEnd_7108861 < baseStart_7108861 := by decide
  rcases family_descends (prefixWord ++ tailWord_7108861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7108885 : List Nat := [1, 3, 2, 1, 2, 1, 3, 3, 3, 1, 3]
def baseStart_7108885 : Nat := 118140960795 + 7108885 * 2 ^ 59
def prefixEnd_7108885 : Nat := 4983230072969 + 3 ^ 40 * 7108885 * 2
def baseEnd_7108885 : Nat := 3650274922537524188444339

theorem tailTrace_7108885 : CollatzResearch.WordTrace tailWord_7108885 prefixEnd_7108885 3650274922537524188444339 := by
  unfold tailWord_7108885
  simp only [CollatzResearch.WordTrace]
  refine ⟨259282336850731220743600109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172854891233820813829066739 259282336850731220743600109)
  ·
    refine ⟨97230876319024207778850041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259282336850731220743600109 97230876319024207778850041)
    ·
      refine ⟨72923157239268155834137531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97230876319024207778850041 72923157239268155834137531)
      ·
        refine ⟨109384735858902233751206297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72923157239268155834137531 109384735858902233751206297)
        ·
          refine ⟨82038551894176675313404723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109384735858902233751206297 82038551894176675313404723)
          ·
            refine ⟨123057827841265012970107085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82038551894176675313404723 123057827841265012970107085)
            ·
              refine ⟨46146685440474379863790157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123057827841265012970107085 46146685440474379863790157)
              ·
                refine ⟨17305007040177892448921309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46146685440474379863790157 17305007040177892448921309)
                ·
                  refine ⟨6489377640066709668345491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17305007040177892448921309 6489377640066709668345491)
                  ·
                    refine ⟨9734066460100064502518237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6489377640066709668345491 9734066460100064502518237)
                    ·
                      refine ⟨3650274922537524188444339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9734066460100064502518237 3650274922537524188444339)
                      ·
                        rfl

theorem cell23_7108885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 3, 3, 1, 3].length) (baseStart_7108885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7108885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7108885 prefixEnd_7108885 := by exact prefixLift 7108885
  have htrace : WordTrace (prefixWord ++ tailWord_7108885) baseStart_7108885 baseEnd_7108885 := by
    simpa [prefixWord, tailWord_7108885, baseEnd_7108885] using wordTrace_append hprefix tailTrace_7108885
  have hstable : (prefixWord ++ tailWord_7108885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7108885).length < 2 ^ (prefixWord ++ tailWord_7108885).sum := by decide
  have hdescent : baseEnd_7108885 < baseStart_7108885 := by decide
  rcases family_descends (prefixWord ++ tailWord_7108885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7108895 : List Nat := [1, 1, 2, 4, 3, 1, 1, 2, 1, 5, 2]
def baseStart_7108895 : Nat := 118140960795 + 7108895 * 2 ^ 59
def prefixEnd_7108895 : Nat := 4983230072969 + 3 ^ 40 * 7108895 * 2
def baseEnd_7108895 : Nat := 3650280057344069149319293

theorem tailTrace_7108895 : CollatzResearch.WordTrace tailWord_7108895 prefixEnd_7108895 3650280057344069149319293 := by
  unfold tailWord_7108895
  simp only [CollatzResearch.WordTrace]
  refine ⟨259282701580694992451464139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172855134387129994967642759 259282701580694992451464139)
  ·
    refine ⟨388924052371042488677196209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259282701580694992451464139 388924052371042488677196209)
    ·
      refine ⟨291693039278281866507897157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 388924052371042488677196209 291693039278281866507897157)
      ·
        refine ⟨54692444864677849970230717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 291693039278281866507897157 54692444864677849970230717)
        ·
          refine ⟨20509666824254193738836519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54692444864677849970230717 20509666824254193738836519)
          ·
            refine ⟨30764500236381290608254779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20509666824254193738836519 30764500236381290608254779)
            ·
              refine ⟨46146750354571935912382169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30764500236381290608254779 46146750354571935912382169)
              ·
                refine ⟨34610062765928951934286627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46146750354571935912382169 34610062765928951934286627)
                ·
                  refine ⟨51915094148893427901429941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34610062765928951934286627 51915094148893427901429941)
                  ·
                    refine ⟨4867040076458758865759057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51915094148893427901429941 4867040076458758865759057)
                    ·
                      refine ⟨3650280057344069149319293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4867040076458758865759057 3650280057344069149319293)
                      ·
                        rfl

theorem cell23_7108895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 5, 2].length) (baseStart_7108895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7108895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7108895 prefixEnd_7108895 := by exact prefixLift 7108895
  have htrace : WordTrace (prefixWord ++ tailWord_7108895) baseStart_7108895 baseEnd_7108895 := by
    simpa [prefixWord, tailWord_7108895, baseEnd_7108895] using wordTrace_append hprefix tailTrace_7108895
  have hstable : (prefixWord ++ tailWord_7108895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7108895).length < 2 ^ (prefixWord ++ tailWord_7108895).sum := by decide
  have hdescent : baseEnd_7108895 < baseStart_7108895 := by decide
  rcases family_descends (prefixWord ++ tailWord_7108895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7108908 : List Nat := [2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 4]
def baseStart_7108908 : Nat := 118140960795 + 7108908 * 2 ^ 59
def prefixEnd_7108908 : Nat := 4983230072969 + 3 ^ 40 * 7108908 * 2
def baseEnd_7108908 : Nat := 3650286732592577598456733

theorem tailTrace_7108908 : CollatzResearch.WordTrace tailWord_7108908 prefixEnd_7108908 3650286732592577598456733 := by
  unfold tailWord_7108908
  simp only [CollatzResearch.WordTrace]
  refine ⟨129641587864823947835843689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172855450486431930447791585 129641587864823947835843689)
  ·
    refine ⟨97231190898617960876882767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129641587864823947835843689 97231190898617960876882767)
    ·
      refine ⟨145846786347926941315324151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97231190898617960876882767 145846786347926941315324151)
      ·
        refine ⟨218770179521890411972986227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145846786347926941315324151 218770179521890411972986227)
        ·
          refine ⟨328155269282835617959479341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218770179521890411972986227 328155269282835617959479341)
          ·
            refine ⟨123058225981063356734804753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 328155269282835617959479341 123058225981063356734804753)
            ·
              refine ⟨92293669485797517551103565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123058225981063356734804753 92293669485797517551103565)
              ·
                refine ⟨34610126057174069081663837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92293669485797517551103565 34610126057174069081663837)
                ·
                  refine ⟨12978797271440275905623939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34610126057174069081663837 12978797271440275905623939)
                  ·
                    refine ⟨19468195907160413858435909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12978797271440275905623939 19468195907160413858435909)
                    ·
                      refine ⟨3650286732592577598456733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19468195907160413858435909 3650286732592577598456733)
                      ·
                        rfl

theorem cell23_7108908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 4].length) (baseStart_7108908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7108908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7108908 prefixEnd_7108908 := by exact prefixLift 7108908
  have htrace : WordTrace (prefixWord ++ tailWord_7108908) baseStart_7108908 baseEnd_7108908 := by
    simpa [prefixWord, tailWord_7108908, baseEnd_7108908] using wordTrace_append hprefix tailTrace_7108908
  have hstable : (prefixWord ++ tailWord_7108908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7108908).length < 2 ^ (prefixWord ++ tailWord_7108908).sum := by decide
  have hdescent : baseEnd_7108908 < baseStart_7108908 := by decide
  rcases family_descends (prefixWord ++ tailWord_7108908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7108929 : List Nat := [1, 2, 5, 2, 2, 1, 1, 2, 2, 3, 2]
def baseStart_7108929 : Nat := 118140960795 + 7108929 * 2 ^ 59
def prefixEnd_7108929 : Nat := 4983230072969 + 3 ^ 40 * 7108929 * 2
def baseEnd_7108929 : Nat := 3650297515686322016294137

theorem tailTrace_7108929 : CollatzResearch.WordTrace tailWord_7108929 prefixEnd_7108929 3650297515686322016294137 := by
  unfold tailWord_7108929
  simp only [CollatzResearch.WordTrace]
  refine ⟨259283941662571816258201841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172855961108381210838801227 259283941662571816258201841)
  ·
    refine ⟨194462956246928862193651381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259283941662571816258201841 194462956246928862193651381)
    ·
      refine ⟨18230902148149580830654817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 194462956246928862193651381 18230902148149580830654817)
      ·
        refine ⟨13673176611112185622991113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18230902148149580830654817 13673176611112185622991113)
        ·
          refine ⟨10254882458334139217243335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13673176611112185622991113 10254882458334139217243335)
          ·
            refine ⟨15382323687501208825865003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10254882458334139217243335 15382323687501208825865003)
            ·
              refine ⟨23073485531251813238797505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15382323687501208825865003 23073485531251813238797505)
              ·
                refine ⟨17305114148438859929098129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23073485531251813238797505 17305114148438859929098129)
                ·
                  refine ⟨12978835611329144946823597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17305114148438859929098129 12978835611329144946823597)
                  ·
                    refine ⟨4867063354248429355058849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12978835611329144946823597 4867063354248429355058849)
                    ·
                      refine ⟨3650297515686322016294137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4867063354248429355058849 3650297515686322016294137)
                      ·
                        rfl

theorem cell23_7108929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_7108929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7108929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7108929 prefixEnd_7108929 := by exact prefixLift 7108929
  have htrace : WordTrace (prefixWord ++ tailWord_7108929) baseStart_7108929 baseEnd_7108929 := by
    simpa [prefixWord, tailWord_7108929, baseEnd_7108929] using wordTrace_append hprefix tailTrace_7108929
  have hstable : (prefixWord ++ tailWord_7108929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7108929).length < 2 ^ (prefixWord ++ tailWord_7108929).sum := by decide
  have hdescent : baseEnd_7108929 < baseStart_7108929 := by decide
  rcases family_descends (prefixWord ++ tailWord_7108929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7108931 : List Nat := [1, 1, 1, 3, 1, 3, 13]
def baseStart_7108931 : Nat := 118140960795 + 7108931 * 2 ^ 59
def prefixEnd_7108931 : Nat := 4983230072969 + 3 ^ 40 * 7108931 * 2
def baseEnd_7108931 : Nat := 45065414106760876647767

theorem tailTrace_7108931 : CollatzResearch.WordTrace tailWord_7108931 prefixEnd_7108931 45065414106760876647767 := by
  unfold tailWord_7108931
  simp only [CollatzResearch.WordTrace]
  refine ⟨259284014608564570599774647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172856009739043047066516431 259284014608564570599774647)
  ·
    refine ⟨388926021912846855899661971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259284014608564570599774647 388926021912846855899661971)
    ·
      refine ⟨583389032869270283849492957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388926021912846855899661971 583389032869270283849492957)
      ·
        refine ⟨218770887325976356443559859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 583389032869270283849492957 218770887325976356443559859)
        ·
          refine ⟨328156330988964534665339789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218770887325976356443559859 328156330988964534665339789)
          ·
            refine ⟨123058624120861700499502421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 328156330988964534665339789 123058624120861700499502421)
            ·
              refine ⟨45065414106760876647767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 123058624120861700499502421 45065414106760876647767)
              ·
                rfl

theorem cell23_7108931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 13].length) (baseStart_7108931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7108931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7108931 prefixEnd_7108931 := by exact prefixLift 7108931
  have htrace : WordTrace (prefixWord ++ tailWord_7108931) baseStart_7108931 baseEnd_7108931 := by
    simpa [prefixWord, tailWord_7108931, baseEnd_7108931] using wordTrace_append hprefix tailTrace_7108931
  have hstable : (prefixWord ++ tailWord_7108931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7108931).length < 2 ^ (prefixWord ++ tailWord_7108931).sum := by decide
  have hdescent : baseEnd_7108931 < baseStart_7108931 := by decide
  rcases family_descends (prefixWord ++ tailWord_7108931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7108935 : List Nat := [1, 1, 4, 1, 2, 2, 2, 4, 2, 4]
def baseStart_7108935 : Nat := 118140960795 + 7108935 * 2 ^ 59
def prefixEnd_7108935 : Nat := 4983230072969 + 3 ^ 40 * 7108935 * 2
def baseEnd_7108935 : Nat := 1216766865523416330939703

theorem tailTrace_7108935 : CollatzResearch.WordTrace tailWord_7108935 prefixEnd_7108935 1216766865523416330939703 := by
  unfold tailWord_7108935
  simp only [CollatzResearch.WordTrace]
  refine ⟨259284160500550079282920259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172856107000366719521946839 259284160500550079282920259)
  ·
    refine ⟨388926240750825118924380389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259284160500550079282920259 388926240750825118924380389)
    ·
      refine ⟨72923670140779709798321323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 388926240750825118924380389 72923670140779709798321323)
      ·
        refine ⟨109385505211169564697481985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72923670140779709798321323 109385505211169564697481985)
        ·
          refine ⟨82039128908377173523111489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109385505211169564697481985 82039128908377173523111489)
          ·
            refine ⟨61529346681282880142333617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82039128908377173523111489 61529346681282880142333617)
            ·
              refine ⟨46147010010962160106750213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61529346681282880142333617 46147010010962160106750213)
              ·
                refine ⟨8652564377055405020015665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46147010010962160106750213 8652564377055405020015665)
                ·
                  refine ⟨6489423282791553765011749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8652564377055405020015665 6489423282791553765011749)
                  ·
                    refine ⟨1216766865523416330939703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6489423282791553765011749 1216766865523416330939703)
                    ·
                      rfl

theorem cell23_7108935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 4, 2, 4].length) (baseStart_7108935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7108935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7108935 prefixEnd_7108935 := by exact prefixLift 7108935
  have htrace : WordTrace (prefixWord ++ tailWord_7108935) baseStart_7108935 baseEnd_7108935 := by
    simpa [prefixWord, tailWord_7108935, baseEnd_7108935] using wordTrace_append hprefix tailTrace_7108935
  have hstable : (prefixWord ++ tailWord_7108935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7108935).length < 2 ^ (prefixWord ++ tailWord_7108935).sum := by decide
  have hdescent : baseEnd_7108935 < baseStart_7108935 := by decide
  rcases family_descends (prefixWord ++ tailWord_7108935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7108942 : List Nat := [4, 1, 1, 1, 1, 1, 2, 5, 3, 2, 2]
def baseStart_7108942 : Nat := 118140960795 + 7108942 * 2 ^ 59
def prefixEnd_7108942 : Nat := 4983230072969 + 3 ^ 40 * 7108942 * 2
def baseEnd_7108942 : Nat := 3650304190934830465431577

theorem tailTrace_7108942 : CollatzResearch.WordTrace tailWord_7108942 prefixEnd_7108942 3650304190934830465431577 := by
  unfold tailWord_7108942
  simp only [CollatzResearch.WordTrace]
  refine ⟨32410551976440589934803135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172856277207683146318950053 32410551976440589934803135)
  ·
    refine ⟨48615827964660884902204703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32410551976440589934803135 48615827964660884902204703)
    ·
      refine ⟨72923741946991327353307055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48615827964660884902204703 72923741946991327353307055)
      ·
        refine ⟨109385612920486991029960583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72923741946991327353307055 109385612920486991029960583)
        ·
          refine ⟨164078419380730486544940875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109385612920486991029960583 164078419380730486544940875)
          ·
            refine ⟨246117629071095729817411313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164078419380730486544940875 246117629071095729817411313)
            ·
              refine ⟨184588221803321797363058485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246117629071095729817411313 184588221803321797363058485)
              ·
                refine ⟨17305145794061418502786733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 184588221803321797363058485 17305145794061418502786733)
                ·
                  refine ⟨6489429672773031938545025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17305145794061418502786733 6489429672773031938545025)
                  ·
                    refine ⟨4867072254579773953908769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6489429672773031938545025 4867072254579773953908769)
                    ·
                      refine ⟨3650304190934830465431577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4867072254579773953908769 3650304190934830465431577)
                      ·
                        rfl

theorem cell23_7108942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 5, 3, 2, 2].length) (baseStart_7108942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7108942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7108942 prefixEnd_7108942 := by exact prefixLift 7108942
  have htrace : WordTrace (prefixWord ++ tailWord_7108942) baseStart_7108942 baseEnd_7108942 := by
    simpa [prefixWord, tailWord_7108942, baseEnd_7108942] using wordTrace_append hprefix tailTrace_7108942
  have hstable : (prefixWord ++ tailWord_7108942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7108942).length < 2 ^ (prefixWord ++ tailWord_7108942).sum := by decide
  have hdescent : baseEnd_7108942 < baseStart_7108942 := by decide
  rcases family_descends (prefixWord ++ tailWord_7108942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7108948 : List Nat := [2, 4, 1, 1, 2, 2, 1, 10]
def baseStart_7108948 : Nat := 118140960795 + 7108948 * 2 ^ 59
def prefixEnd_7108948 : Nat := 4983230072969 + 3 ^ 40 * 7108948 * 2
def baseEnd_7108948 : Nat := 135196565622916942294687

theorem tailTrace_7108948 : CollatzResearch.WordTrace tailWord_7108948 prefixEnd_7108948 135196565622916942294687 := by
  unfold tailWord_7108948
  simp only [CollatzResearch.WordTrace]
  refine ⟨129642317324751491251571749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172856423099668655002095665 129642317324751491251571749)
  ·
    refine ⟨24307934498390904609669703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 129642317324751491251571749 24307934498390904609669703)
    ·
      refine ⟨36461901747586356914504555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24307934498390904609669703 36461901747586356914504555)
      ·
        refine ⟨54692852621379535371756833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36461901747586356914504555 54692852621379535371756833)
        ·
          refine ⟨41019639466034651528817625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54692852621379535371756833 41019639466034651528817625)
          ·
            refine ⟨30764729599525988646613219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41019639466034651528817625 30764729599525988646613219)
            ·
              refine ⟨46147094399288982969919829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30764729599525988646613219 46147094399288982969919829)
              ·
                refine ⟨135196565622916942294687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 46147094399288982969919829 135196565622916942294687)
                ·
                  rfl

theorem cell23_7108948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 10].length) (baseStart_7108948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7108948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7108948 prefixEnd_7108948 := by exact prefixLift 7108948
  have htrace : WordTrace (prefixWord ++ tailWord_7108948) baseStart_7108948 baseEnd_7108948 := by
    simpa [prefixWord, tailWord_7108948, baseEnd_7108948] using wordTrace_append hprefix tailTrace_7108948
  have hstable : (prefixWord ++ tailWord_7108948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7108948).length < 2 ^ (prefixWord ++ tailWord_7108948).sum := by decide
  have hdescent : baseEnd_7108948 < baseStart_7108948 := by decide
  rcases family_descends (prefixWord ++ tailWord_7108948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7108956 : List Nat := [2, 2, 4, 3, 2, 1, 1, 2, 1, 5]
def baseStart_7108956 : Nat := 118140960795 + 7108956 * 2 ^ 59
def prefixEnd_7108956 : Nat := 4983230072969 + 3 ^ 40 * 7108956 * 2
def baseEnd_7108956 : Nat := 1216770459887997803552171

theorem tailTrace_7108956 : CollatzResearch.WordTrace tailWord_7108956 prefixEnd_7108956 1216770459887997803552171 := by
  unfold tailWord_7108956
  simp only [CollatzResearch.WordTrace]
  refine ⟨129642463216736999934717361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 172856617622315999912956481 129642463216736999934717361)
  ·
    refine ⟨97231847412552749951038021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 129642463216736999934717361 97231847412552749951038021)
    ·
      refine ⟨18230971389853640615819629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97231847412552749951038021 18230971389853640615819629)
      ·
        refine ⟨6836614271195115230932361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18230971389853640615819629 6836614271195115230932361)
        ·
          refine ⟨5127460703396336423199271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6836614271195115230932361 5127460703396336423199271)
          ·
            refine ⟨7691191055094504634798907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5127460703396336423199271 7691191055094504634798907)
            ·
              refine ⟨11536786582641756952198361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7691191055094504634798907 11536786582641756952198361)
              ·
                refine ⟨8652589936981317714148771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11536786582641756952198361 8652589936981317714148771)
                ·
                  refine ⟨12978884905471976571223157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8652589936981317714148771 12978884905471976571223157)
                  ·
                    refine ⟨1216770459887997803552171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12978884905471976571223157 1216770459887997803552171)
                    ·
                      rfl

theorem cell23_7108956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_7108956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7108956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7108956 prefixEnd_7108956 := by exact prefixLift 7108956
  have htrace : WordTrace (prefixWord ++ tailWord_7108956) baseStart_7108956 baseEnd_7108956 := by
    simpa [prefixWord, tailWord_7108956, baseEnd_7108956] using wordTrace_append hprefix tailTrace_7108956
  have hstable : (prefixWord ++ tailWord_7108956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7108956).length < 2 ^ (prefixWord ++ tailWord_7108956).sum := by decide
  have hdescent : baseEnd_7108956 < baseStart_7108956 := by decide
  rcases family_descends (prefixWord ++ tailWord_7108956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7108962 : List Nat := [3, 3, 2, 1, 1, 3, 1, 1, 3, 2, 3]
def baseStart_7108962 : Nat := 118140960795 + 7108962 * 2 ^ 59
def prefixEnd_7108962 : Nat := 4983230072969 + 3 ^ 40 * 7108962 * 2
def baseEnd_7108962 : Nat := 3650314460547920387181485

theorem tailTrace_7108962 : CollatzResearch.WordTrace tailWord_7108962 prefixEnd_7108962 3650314460547920387181485 := by
  unfold tailWord_7108962
  simp only [CollatzResearch.WordTrace]
  refine ⟨64821286317863065723538285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172856763514301508596102093 64821286317863065723538285)
  ·
    refine ⟨24307982369198649646326857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64821286317863065723538285 24307982369198649646326857)
    ·
      refine ⟨18230986776898987234745143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24307982369198649646326857 18230986776898987234745143)
      ·
        refine ⟨27346480165348480852117715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18230986776898987234745143 27346480165348480852117715)
        ·
          refine ⟨41019720248022721278176573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27346480165348480852117715 41019720248022721278176573)
          ·
            refine ⟨15382395093008520479316215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41019720248022721278176573 15382395093008520479316215)
            ·
              refine ⟨23073592639512780718974323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15382395093008520479316215 23073592639512780718974323)
              ·
                refine ⟨34610388959269171078461485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23073592639512780718974323 34610388959269171078461485)
                ·
                  refine ⟨12978895859725939154423057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34610388959269171078461485 12978895859725939154423057)
                  ·
                    refine ⟨9734171894794454365817293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12978895859725939154423057 9734171894794454365817293)
                    ·
                      refine ⟨3650314460547920387181485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9734171894794454365817293 3650314460547920387181485)
                      ·
                        rfl

theorem cell23_7108962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_7108962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7108962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7108962 prefixEnd_7108962 := by exact prefixLift 7108962
  have htrace : WordTrace (prefixWord ++ tailWord_7108962) baseStart_7108962 baseEnd_7108962 := by
    simpa [prefixWord, tailWord_7108962, baseEnd_7108962] using wordTrace_append hprefix tailTrace_7108962
  have hstable : (prefixWord ++ tailWord_7108962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7108962).length < 2 ^ (prefixWord ++ tailWord_7108962).sum := by decide
  have hdescent : baseEnd_7108962 < baseStart_7108962 := by decide
  rcases family_descends (prefixWord ++ tailWord_7108962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7108975 : List Nat := [1, 1, 2, 1, 3, 1, 2, 4, 4, 1, 3]
def baseStart_7108975 : Nat := 118140960795 + 7108975 * 2 ^ 59
def prefixEnd_7108975 : Nat := 4983230072969 + 3 ^ 40 * 7108975 * 2
def baseEnd_7108975 : Nat := 3650321135796428836318925

theorem tailTrace_7108975 : CollatzResearch.WordTrace tailWord_7108975 prefixEnd_7108975 3650321135796428836318925 := by
  unfold tailWord_7108975
  simp only [CollatzResearch.WordTrace]
  refine ⟨259285619420405166114376379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172857079613603444076250919 259285619420405166114376379)
  ·
    refine ⟨388928429130607749171564569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259285619420405166114376379 388928429130607749171564569)
    ·
      refine ⟨291696321847955811878673427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 388928429130607749171564569 291696321847955811878673427)
      ·
        refine ⟨437544482771933717818010141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291696321847955811878673427 437544482771933717818010141)
        ·
          refine ⟨164079181039475144181753803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 437544482771933717818010141 164079181039475144181753803)
          ·
            refine ⟨246118771559212716272630705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164079181039475144181753803 246118771559212716272630705)
            ·
              refine ⟨184589078669409537204473029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246118771559212716272630705 184589078669409537204473029)
              ·
                refine ⟨34610452250514288225838693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 184589078669409537204473029 34610452250514288225838693)
                ·
                  refine ⟨6489459796971429042344755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34610452250514288225838693 6489459796971429042344755)
                  ·
                    refine ⟨9734189695457143563517133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6489459796971429042344755 9734189695457143563517133)
                    ·
                      refine ⟨3650321135796428836318925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9734189695457143563517133 3650321135796428836318925)
                      ·
                        rfl

theorem cell23_7108975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 4, 1, 3].length) (baseStart_7108975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7108975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7108975 prefixEnd_7108975 := by exact prefixLift 7108975
  have htrace : WordTrace (prefixWord ++ tailWord_7108975) baseStart_7108975 baseEnd_7108975 := by
    simpa [prefixWord, tailWord_7108975, baseEnd_7108975] using wordTrace_append hprefix tailTrace_7108975
  have hstable : (prefixWord ++ tailWord_7108975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7108975).length < 2 ^ (prefixWord ++ tailWord_7108975).sum := by decide
  have hdescent : baseEnd_7108975 < baseStart_7108975 := by decide
  rcases family_descends (prefixWord ++ tailWord_7108975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7108982 : List Nat := [5, 1, 1, 4, 2, 10]
def baseStart_7108982 : Nat := 118140960795 + 7108982 * 2 ^ 59
def prefixEnd_7108982 : Nat := 4983230072969 + 3 ^ 40 * 7108982 * 2
def baseEnd_7108982 : Nat := 15021912469798396333051

theorem tailTrace_7108982 : CollatzResearch.WordTrace tailWord_7108982 prefixEnd_7108982 15021912469798396333051 := by
  unfold tailWord_7108982
  simp only [CollatzResearch.WordTrace]
  refine ⟨16205367170711237894367575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 172857249820919870873254133 16205367170711237894367575)
  ·
    refine ⟨24308050756066856841551363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16205367170711237894367575 24308050756066856841551363)
    ·
      refine ⟨36462076134100285262327045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24308050756066856841551363 36462076134100285262327045)
      ·
        refine ⟨6836639275143803486686321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36462076134100285262327045 6836639275143803486686321)
        ·
          refine ⟨5127479456357852615014741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6836639275143803486686321 5127479456357852615014741)
          ·
            refine ⟨15021912469798396333051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5127479456357852615014741 15021912469798396333051)
            ·
              rfl

theorem cell23_7108982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 10].length) (baseStart_7108982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7108982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7108982 prefixEnd_7108982 := by exact prefixLift 7108982
  have htrace : WordTrace (prefixWord ++ tailWord_7108982) baseStart_7108982 baseEnd_7108982 := by
    simpa [prefixWord, tailWord_7108982, baseEnd_7108982] using wordTrace_append hprefix tailTrace_7108982
  have hstable : (prefixWord ++ tailWord_7108982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7108982).length < 2 ^ (prefixWord ++ tailWord_7108982).sum := by decide
  have hdescent : baseEnd_7108982 < baseStart_7108982 := by decide
  rcases family_descends (prefixWord ++ tailWord_7108982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7108993 : List Nat := [1, 2, 4, 3, 1, 1, 4, 2, 1, 2, 2]
def baseStart_7108993 : Nat := 118140960795 + 7108993 * 2 ^ 59
def prefixEnd_7108993 : Nat := 4983230072969 + 3 ^ 40 * 7108993 * 2
def baseEnd_7108993 : Nat := 3650330378448209765893843

theorem tailTrace_7108993 : CollatzResearch.WordTrace tailWord_7108993 prefixEnd_7108993 3650330378448209765893843 := by
  unfold tailWord_7108993
  simp only [CollatzResearch.WordTrace]
  refine ⟨259286275934339955188531633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172857517289559970125687755 259286275934339955188531633)
  ·
    refine ⟨194464706950754966391398725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259286275934339955188531633 194464706950754966391398725)
    ·
      refine ⟨36462132553266556198387261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 194464706950754966391398725 36462132553266556198387261)
      ·
        refine ⟨13673299707474958574395223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36462132553266556198387261 13673299707474958574395223)
        ·
          refine ⟨20509949561212437861592835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13673299707474958574395223 20509949561212437861592835)
          ·
            refine ⟨30764924341818656792389253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20509949561212437861592835 30764924341818656792389253)
            ·
              refine ⟨5768423314090998148572985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30764924341818656792389253 5768423314090998148572985)
              ·
                refine ⟨4326317485568248611429739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5768423314090998148572985 4326317485568248611429739)
                ·
                  refine ⟨6489476228352372917144609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4326317485568248611429739 6489476228352372917144609)
                  ·
                    refine ⟨4867107171264279687858457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6489476228352372917144609 4867107171264279687858457)
                    ·
                      refine ⟨3650330378448209765893843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4867107171264279687858457 3650330378448209765893843)
                      ·
                        rfl

theorem cell23_7108993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_7108993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7108993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7108993 prefixEnd_7108993 := by exact prefixLift 7108993
  have htrace : WordTrace (prefixWord ++ tailWord_7108993) baseStart_7108993 baseEnd_7108993 := by
    simpa [prefixWord, tailWord_7108993, baseEnd_7108993] using wordTrace_append hprefix tailTrace_7108993
  have hstable : (prefixWord ++ tailWord_7108993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7108993).length < 2 ^ (prefixWord ++ tailWord_7108993).sum := by decide
  have hdescent : baseEnd_7108993 < baseStart_7108993 := by decide
  rcases family_descends (prefixWord ++ tailWord_7108993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7109049 : List Nat := [1, 2, 1, 4, 3, 2, 1, 1, 4, 2, 2]
def baseStart_7109049 : Nat := 118140960795 + 7109049 * 2 ^ 59
def prefixEnd_7109049 : Nat := 4983230072969 + 3 ^ 40 * 7109049 * 2
def baseEnd_7109049 : Nat := 3650359133364861546793585

theorem tailTrace_7109049 : CollatzResearch.WordTrace tailWord_7109049 prefixEnd_7109049 3650359133364861546793585 := by
  unfold tailWord_7109049
  simp only [CollatzResearch.WordTrace]
  refine ⟨259288318422137076752570201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172858878948091384501713467 259288318422137076752570201)
  ·
    refine ⟨194466238816602807564427651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259288318422137076752570201 194466238816602807564427651)
    ·
      refine ⟨291699358224904211346641477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194466238816602807564427651 291699358224904211346641477)
      ·
        refine ⟨54693629667169539627495277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 291699358224904211346641477 54693629667169539627495277)
        ·
          refine ⟨20510111125188577360310729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54693629667169539627495277 20510111125188577360310729)
          ·
            refine ⟨15382583343891433020233047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20510111125188577360310729 15382583343891433020233047)
            ·
              refine ⟨23073875015837149530349571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15382583343891433020233047 23073875015837149530349571)
              ·
                refine ⟨34610812523755724295524357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23073875015837149530349571 34610812523755724295524357)
                ·
                  refine ⟨6489527348204198305410817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34610812523755724295524357 6489527348204198305410817)
                  ·
                    refine ⟨4867145511153148729058113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6489527348204198305410817 4867145511153148729058113)
                    ·
                      refine ⟨3650359133364861546793585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4867145511153148729058113 3650359133364861546793585)
                      ·
                        rfl

theorem cell23_7109049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 4, 2, 2].length) (baseStart_7109049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7109049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7109049 prefixEnd_7109049 := by exact prefixLift 7109049
  have htrace : WordTrace (prefixWord ++ tailWord_7109049) baseStart_7109049 baseEnd_7109049 := by
    simpa [prefixWord, tailWord_7109049, baseEnd_7109049] using wordTrace_append hprefix tailTrace_7109049
  have hstable : (prefixWord ++ tailWord_7109049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7109049).length < 2 ^ (prefixWord ++ tailWord_7109049).sum := by decide
  have hdescent : baseEnd_7109049 < baseStart_7109049 := by decide
  rcases family_descends (prefixWord ++ tailWord_7109049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7109065 : List Nat := [1, 2, 1, 1, 2, 1, 6, 1, 2, 3, 3]
def baseStart_7109065 : Nat := 118140960795 + 7109065 * 2 ^ 59
def prefixEnd_7109065 : Nat := 4983230072969 + 3 ^ 40 * 7109065 * 2
def baseEnd_7109065 : Nat := 3650367349055333484193511

theorem tailTrace_7109065 : CollatzResearch.WordTrace tailWord_7109065 prefixEnd_7109065 3650367349055333484193511 := by
  unfold tailWord_7109065
  simp only [CollatzResearch.WordTrace]
  refine ⟨259288901990079111485152649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172859267993386074323435099 259288901990079111485152649)
  ·
    refine ⟨194466676492559333613864487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259288901990079111485152649 194466676492559333613864487)
    ·
      refine ⟨291700014738839000420796731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194466676492559333613864487 291700014738839000420796731)
      ·
        refine ⟨437550022108258500631195097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291700014738839000420796731 437550022108258500631195097)
        ·
          refine ⟨328162516581193875473396323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 437550022108258500631195097 328162516581193875473396323)
          ·
            refine ⟨492243774871790813210094485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328162516581193875473396323 492243774871790813210094485)
            ·
              refine ⟨23073926947115194369223179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 492243774871790813210094485 23073926947115194369223179)
              ·
                refine ⟨34610890420672791553834769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23073926947115194369223179 34610890420672791553834769)
                ·
                  refine ⟨25958167815504593665376077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34610890420672791553834769 25958167815504593665376077)
                  ·
                    refine ⟨9734312930814222624516029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25958167815504593665376077 9734312930814222624516029)
                    ·
                      refine ⟨3650367349055333484193511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9734312930814222624516029 3650367349055333484193511)
                      ·
                        rfl

theorem cell23_7109065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 2, 3, 3].length) (baseStart_7109065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7109065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7109065 prefixEnd_7109065 := by exact prefixLift 7109065
  have htrace : WordTrace (prefixWord ++ tailWord_7109065) baseStart_7109065 baseEnd_7109065 := by
    simpa [prefixWord, tailWord_7109065, baseEnd_7109065] using wordTrace_append hprefix tailTrace_7109065
  have hstable : (prefixWord ++ tailWord_7109065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7109065).length < 2 ^ (prefixWord ++ tailWord_7109065).sum := by decide
  have hdescent : baseEnd_7109065 < baseStart_7109065 := by decide
  rcases family_descends (prefixWord ++ tailWord_7109065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7109066 : List Nat := [3, 1, 2, 1, 2, 2, 5, 1, 2, 2, 2]
def baseStart_7109066 : Nat := 118140960795 + 7109066 * 2 ^ 59
def prefixEnd_7109066 : Nat := 4983230072969 + 3 ^ 40 * 7109066 * 2
def baseEnd_7109066 : Nat := 3650367862535987980281007

theorem tailTrace_7109066 : CollatzResearch.WordTrace tailWord_7109066 prefixEnd_7109066 3650367862535987980281007 := by
  unfold tailWord_7109066
  simp only [CollatzResearch.WordTrace]
  refine ⟨64822234615768872163984763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172859292308716992437292701 64822234615768872163984763)
  ·
    refine ⟨97233351923653308245977145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64822234615768872163984763 97233351923653308245977145)
    ·
      refine ⟨72925013942739981184482859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97233351923653308245977145 72925013942739981184482859)
      ·
        refine ⟨109387520914109971776724289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72925013942739981184482859 109387520914109971776724289)
        ·
          refine ⟨82040640685582478832543217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109387520914109971776724289 82040640685582478832543217)
          ·
            refine ⟨61530480514186859124407413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82040640685582478832543217 61530480514186859124407413)
            ·
              refine ⟨5768482548205018042913195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61530480514186859124407413 5768482548205018042913195)
              ·
                refine ⟨8652723822307527064369793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5768482548205018042913195 8652723822307527064369793)
                ·
                  refine ⟨6489542866730645298277345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8652723822307527064369793 6489542866730645298277345)
                  ·
                    refine ⟨4867157150047983973708009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6489542866730645298277345 4867157150047983973708009)
                    ·
                      refine ⟨3650367862535987980281007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4867157150047983973708009 3650367862535987980281007)
                      ·
                        rfl

theorem cell23_7109066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 5, 1, 2, 2, 2].length) (baseStart_7109066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7109066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7109066 prefixEnd_7109066 := by exact prefixLift 7109066
  have htrace : WordTrace (prefixWord ++ tailWord_7109066) baseStart_7109066 baseEnd_7109066 := by
    simpa [prefixWord, tailWord_7109066, baseEnd_7109066] using wordTrace_append hprefix tailTrace_7109066
  have hstable : (prefixWord ++ tailWord_7109066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7109066).length < 2 ^ (prefixWord ++ tailWord_7109066).sum := by decide
  have hdescent : baseEnd_7109066 < baseStart_7109066 := by decide
  rcases family_descends (prefixWord ++ tailWord_7109066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7109075 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 5, 7, 2]
def baseStart_7109075 : Nat := 118140960795 + 7109075 * 2 ^ 59
def prefixEnd_7109075 : Nat := 4983230072969 + 3 ^ 40 * 7109075 * 2
def baseEnd_7109075 : Nat := 3650372483861878445068465

theorem tailTrace_7109075 : CollatzResearch.WordTrace tailWord_7109075 prefixEnd_7109075 3650372483861878445068465 := by
  unfold tailWord_7109075
  simp only [CollatzResearch.WordTrace]
  refine ⟨259289266720042883193016679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172859511146695255462011119 259289266720042883193016679)
  ·
    refine ⟨388933900080064324789525019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259289266720042883193016679 388933900080064324789525019)
    ·
      refine ⟨583400850120096487184287529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388933900080064324789525019 583400850120096487184287529)
      ·
        refine ⟨437550637590072365388215647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 583400850120096487184287529 437550637590072365388215647)
        ·
          refine ⟨656325956385108548082323471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 437550637590072365388215647 656325956385108548082323471)
          ·
            refine ⟨984488934577662822123485207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 656325956385108548082323471 984488934577662822123485207)
            ·
              refine ⟨1476733401866494233185227811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 984488934577662822123485207 1476733401866494233185227811)
              ·
                refine ⟨2215100102799741349777841717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1476733401866494233185227811 2215100102799741349777841717)
                ·
                  refine ⟨207665634637475751541672661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2215100102799741349777841717 207665634637475751541672661)
                  ·
                    refine ⟨4867163311815837926757953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 207665634637475751541672661 4867163311815837926757953)
                    ·
                      refine ⟨3650372483861878445068465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4867163311815837926757953 3650372483861878445068465)
                      ·
                        rfl

theorem cell23_7109075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 7, 2].length) (baseStart_7109075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7109075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7109075 prefixEnd_7109075 := by exact prefixLift 7109075
  have htrace : WordTrace (prefixWord ++ tailWord_7109075) baseStart_7109075 baseEnd_7109075 := by
    simpa [prefixWord, tailWord_7109075, baseEnd_7109075] using wordTrace_append hprefix tailTrace_7109075
  have hstable : (prefixWord ++ tailWord_7109075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7109075).length < 2 ^ (prefixWord ++ tailWord_7109075).sum := by decide
  have hdescent : baseEnd_7109075 < baseStart_7109075 := by decide
  rcases family_descends (prefixWord ++ tailWord_7109075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7109085 : List Nat := [1, 4, 3, 1, 1, 1, 1, 3, 1, 7]
def baseStart_7109085 : Nat := 118140960795 + 7109085 * 2 ^ 59
def prefixEnd_7109085 : Nat := 4983230072969 + 3 ^ 40 * 7109085 * 2
def baseEnd_7109085 : Nat := 1216792539556141135314473

theorem tailTrace_7109085 : CollatzResearch.WordTrace tailWord_7109085 prefixEnd_7109085 1216792539556141135314473 := by
  unfold tailWord_7109085
  simp only [CollatzResearch.WordTrace]
  refine ⟨259289631450006654900880709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172859754300004436600587139 259289631450006654900880709)
  ·
    refine ⟨48616805896876247793915133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 259289631450006654900880709 48616805896876247793915133)
    ·
      refine ⟨18231302211328592922718175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48616805896876247793915133 18231302211328592922718175)
      ·
        refine ⟨27346953316992889384077263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18231302211328592922718175 27346953316992889384077263)
        ·
          refine ⟨41020429975489334076115895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27346953316992889384077263 41020429975489334076115895)
          ·
            refine ⟨61530644963234001114173843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41020429975489334076115895 61530644963234001114173843)
            ·
              refine ⟨92295967444851001671260765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61530644963234001114173843 92295967444851001671260765)
              ·
                refine ⟨34610987791819125626722787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92295967444851001671260765 34610987791819125626722787)
                ·
                  refine ⟨51916481687728688440084181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34610987791819125626722787 51916481687728688440084181)
                  ·
                    refine ⟨1216792539556141135314473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51916481687728688440084181 1216792539556141135314473)
                    ·
                      rfl

theorem cell23_7109085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_7109085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7109085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7109085 prefixEnd_7109085 := by exact prefixLift 7109085
  have htrace : WordTrace (prefixWord ++ tailWord_7109085) baseStart_7109085 baseEnd_7109085 := by
    simpa [prefixWord, tailWord_7109085, baseEnd_7109085] using wordTrace_append hprefix tailTrace_7109085
  have hstable : (prefixWord ++ tailWord_7109085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7109085).length < 2 ^ (prefixWord ++ tailWord_7109085).sum := by decide
  have hdescent : baseEnd_7109085 < baseStart_7109085 := by decide
  rcases family_descends (prefixWord ++ tailWord_7109085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7109095 : List Nat := [1, 1, 5, 2, 1, 1, 2, 2, 1, 2, 5]
def baseStart_7109095 : Nat := 118140960795 + 7109095 * 2 ^ 59
def prefixEnd_7109095 : Nat := 4983230072969 + 3 ^ 40 * 7109095 * 2
def baseEnd_7109095 : Nat := 3650382753474968366818373

theorem tailTrace_7109095 : CollatzResearch.WordTrace tailWord_7109095 prefixEnd_7109095 3650382753474968366818373 := by
  unfold tailWord_7109095
  simp only [CollatzResearch.WordTrace]
  refine ⟨259289996179970426608744739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172859997453313617739163159 259289996179970426608744739)
  ·
    refine ⟨388934994269955639913117109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259289996179970426608744739 388934994269955639913117109)
    ·
      refine ⟨36462655712808341241854729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 388934994269955639913117109 36462655712808341241854729)
      ·
        refine ⟨27346991784606255931391047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36462655712808341241854729 27346991784606255931391047)
        ·
          refine ⟨41020487676909383897086571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27346991784606255931391047 41020487676909383897086571)
          ·
            refine ⟨61530731515364075845629857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41020487676909383897086571 61530731515364075845629857)
            ·
              refine ⟨46148048636523056884222393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61530731515364075845629857 46148048636523056884222393)
              ·
                refine ⟨34611036477392292663166795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46148048636523056884222393 34611036477392292663166795)
                ·
                  refine ⟨51916554716088438994750193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34611036477392292663166795 51916554716088438994750193)
                  ·
                    refine ⟨38937416037066329246062645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51916554716088438994750193 38937416037066329246062645)
                    ·
                      refine ⟨3650382753474968366818373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38937416037066329246062645 3650382753474968366818373)
                      ·
                        rfl

theorem cell23_7109095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_7109095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7109095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7109095 prefixEnd_7109095 := by exact prefixLift 7109095
  have htrace : WordTrace (prefixWord ++ tailWord_7109095) baseStart_7109095 baseEnd_7109095 := by
    simpa [prefixWord, tailWord_7109095, baseEnd_7109095] using wordTrace_append hprefix tailTrace_7109095
  have hstable : (prefixWord ++ tailWord_7109095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7109095).length < 2 ^ (prefixWord ++ tailWord_7109095).sum := by decide
  have hdescent : baseEnd_7109095 < baseStart_7109095 := by decide
  rcases family_descends (prefixWord ++ tailWord_7109095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7109102 : List Nat := [4, 1, 2, 1, 2, 3, 1, 2, 2, 5]
def baseStart_7109102 : Nat := 118140960795 + 7109102 * 2 ^ 59
def prefixEnd_7109102 : Nat := 4983230072969 + 3 ^ 40 * 7109102 * 2
def baseEnd_7109102 : Nat := 1216795449279849946476947

theorem tailTrace_7109102 : CollatzResearch.WordTrace tailWord_7109102 prefixEnd_7109102 1216795449279849946476947 := by
  unfold tailWord_7109102
  simp only [CollatzResearch.WordTrace]
  refine ⟨32411281436368133350531195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 172860167660630044536166373 32411281436368133350531195)
  ·
    refine ⟨48616922154552200025796793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32411281436368133350531195 48616922154552200025796793)
    ·
      refine ⟨36462691615914150019347595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48616922154552200025796793 36462691615914150019347595)
      ·
        refine ⟨54694037423871225029021393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36462691615914150019347595 54694037423871225029021393)
        ·
          refine ⟨41020528067903418771766045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54694037423871225029021393 41020528067903418771766045)
          ·
            refine ⟨15382698025463782039412267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41020528067903418771766045 15382698025463782039412267)
            ·
              refine ⟨23074047038195673059118401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15382698025463782039412267 23074047038195673059118401)
              ·
                refine ⟨17305535278646754794338801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23074047038195673059118401 17305535278646754794338801)
                ·
                  refine ⟨12979151458985066095754101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17305535278646754794338801 12979151458985066095754101)
                  ·
                    refine ⟨1216795449279849946476947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12979151458985066095754101 1216795449279849946476947)
                    ·
                      rfl

theorem cell23_7109102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_7109102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7109102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7109102 prefixEnd_7109102 := by exact prefixLift 7109102
  have htrace : WordTrace (prefixWord ++ tailWord_7109102) baseStart_7109102 baseEnd_7109102 := by
    simpa [prefixWord, tailWord_7109102, baseEnd_7109102] using wordTrace_append hprefix tailTrace_7109102
  have hstable : (prefixWord ++ tailWord_7109102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7109102).length < 2 ^ (prefixWord ++ tailWord_7109102).sum := by decide
  have hdescent : baseEnd_7109102 < baseStart_7109102 := by decide
  rcases family_descends (prefixWord ++ tailWord_7109102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7109106 : List Nat := [3, 2, 1, 4, 2, 1, 3, 2, 5]
def baseStart_7109106 : Nat := 118140960795 + 7109106 * 2 ^ 59
def prefixEnd_7109106 : Nat := 4983230072969 + 3 ^ 40 * 7109106 * 2
def baseEnd_7109106 : Nat := 405598711306907535975647

theorem tailTrace_7109106 : CollatzResearch.WordTrace tailWord_7109106 prefixEnd_7109106 405598711306907535975647 := by
  unfold tailWord_7109106
  simp only [CollatzResearch.WordTrace]
  refine ⟨64822599345732643871848793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 172860264921953716991596781 64822599345732643871848793)
  ·
    refine ⟨48616949509299482903886595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64822599345732643871848793 48616949509299482903886595)
    ·
      refine ⟨72925424263949224355829893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48616949509299482903886595 72925424263949224355829893)
      ·
        refine ⟨13673517049490479566718105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72925424263949224355829893 13673517049490479566718105)
        ·
          refine ⟨10255137787117859675038579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13673517049490479566718105 10255137787117859675038579)
          ·
            refine ⟨15382706680676789512557869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10255137787117859675038579 15382706680676789512557869)
            ·
              refine ⟨5768515005253796067209201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15382706680676789512557869 5768515005253796067209201)
              ·
                refine ⟨4326386253940347050406901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5768515005253796067209201 4326386253940347050406901)
                ·
                  refine ⟨405598711306907535975647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4326386253940347050406901 405598711306907535975647)
                  ·
                    rfl

theorem cell23_7109106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 3, 2, 5].length) (baseStart_7109106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7109106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7109106 prefixEnd_7109106 := by exact prefixLift 7109106
  have htrace : WordTrace (prefixWord ++ tailWord_7109106) baseStart_7109106 baseEnd_7109106 := by
    simpa [prefixWord, tailWord_7109106, baseEnd_7109106] using wordTrace_append hprefix tailTrace_7109106
  have hstable : (prefixWord ++ tailWord_7109106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7109106).length < 2 ^ (prefixWord ++ tailWord_7109106).sum := by decide
  have hdescent : baseEnd_7109106 < baseStart_7109106 := by decide
  rcases family_descends (prefixWord ++ tailWord_7109106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7109125 : List Nat := [1, 3, 1, 1, 2, 2, 2, 1, 3, 4, 3]
def baseStart_7109125 : Nat := 118140960795 + 7109125 * 2 ^ 59
def prefixEnd_7109125 : Nat := 4983230072969 + 3 ^ 40 * 7109125 * 2
def baseEnd_7109125 : Nat := 3650398157894603249443235

theorem tailTrace_7109125 : CollatzResearch.WordTrace tailWord_7109125 prefixEnd_7109125 3650398157894603249443235 := by
  unfold tailWord_7109125
  simp only [CollatzResearch.WordTrace]
  refine ⟨259291090369861741732336829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 172860726913241161154891219 259291090369861741732336829)
  ·
    refine ⟨97234158888698153149626311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 259291090369861741732336829 97234158888698153149626311)
    ·
      refine ⟨145851238333047229724439467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97234158888698153149626311 145851238333047229724439467)
      ·
        refine ⟨218776857499570844586659201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145851238333047229724439467 218776857499570844586659201)
        ·
          refine ⟨164082643124678133439994401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218776857499570844586659201 164082643124678133439994401)
          ·
            refine ⟨123061982343508600079995801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164082643124678133439994401 123061982343508600079995801)
            ·
              refine ⟨92296486757631450059996851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123061982343508600079995801 92296486757631450059996851)
              ·
                refine ⟨138444730136447175089995277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92296486757631450059996851 138444730136447175089995277)
                ·
                  refine ⟨51916773801167690658748229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 138444730136447175089995277 51916773801167690658748229)
                  ·
                    refine ⟨9734395087718941998515293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51916773801167690658748229 9734395087718941998515293)
                    ·
                      refine ⟨3650398157894603249443235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9734395087718941998515293 3650398157894603249443235)
                      ·
                        rfl

theorem cell23_7109125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 4, 3].length) (baseStart_7109125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7109125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7109125 prefixEnd_7109125 := by exact prefixLift 7109125
  have htrace : WordTrace (prefixWord ++ tailWord_7109125) baseStart_7109125 baseEnd_7109125 := by
    simpa [prefixWord, tailWord_7109125, baseEnd_7109125] using wordTrace_append hprefix tailTrace_7109125
  have hstable : (prefixWord ++ tailWord_7109125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7109125).length < 2 ^ (prefixWord ++ tailWord_7109125).sum := by decide
  have hdescent : baseEnd_7109125 < baseStart_7109125 := by decide
  rcases family_descends (prefixWord ++ tailWord_7109125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
